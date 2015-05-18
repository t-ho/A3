package syms;

import source.ErrorHandler;
import source.Position;
import syms.Type.ReferenceType;
import tree.ConstExp;

/** This class provides the individual entries that go in a symbol table.
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 * The kinds of entries are constants, types, variables and procedures.
 * It provides subclasses for each of these kinds.
 * All entries have an identifier, the position (in the source input)
 * of the definition of the identifier, a scope in which it was declared 
 * and a type.
 * The declared type may be a type identifier which needs to be resolved
 * (looked up in the symbol table) to get its corresponding real type.
 * Resolving types is a little tricky because the syntax does not rule out
 * circular references.
 * Particular kinds of entries have additional fields. 
 */
public abstract class SymEntry {
    /** Name of the entry */
    protected String ident;
    /** position of declaration in source input */
    protected Position pos;
    /** scope in which declared */
    protected Scope scope;
    /** type of the identifier after type resolution */
    protected Type type;
    /** whether id has been resolved and space allocated where necessary */
    protected boolean resolved;
    /* All entries have all the above fields. */
    
    /** Only subclasses of SymEntry have public constructors. */
    private SymEntry( String id, Position p, Scope s, Type t, boolean r ) {
        ident = id;
        pos = p;
        scope = s;
        type = t;
        resolved = r;
    }
    public String getIdent() {
        return ident;
    }
    public Position getPosition() {
        return pos;
    }
    public void setScope( Scope scope ) {
        this.scope = scope;
    }
    public int getLevel() {
        return scope.getLevel();
    }
    /** @return the type of the entry.
     * May need to resolve type entry first.
     */
    public Type getType() {
        if( !resolved ) {
            resolve();
        }
        return type;
    }
    public void setType( Type t ) {
        this.type = t;
    }
    /** Resolve any references to type identifiers in supplied scope */
    public void resolve() {
        if( ! resolved ) {
            type = type.resolveType( pos );
            resolved = true;
        }
    }
    /** For debugging */
    protected String toString( String kind, String sep ) {
        return kind + " " + ident + sep + type + " level " + 
                scope.getLevel();
    }
    /** Symbol table entry for a CONST identifier */
    public static class ConstantEntry extends SymEntry {
        /** The value of the constant represented as an integer. */
        int value;
        /** Expression tree for constant before it is evaluated */
        ConstExp tree;
        /** Status of constant for resolving references */
        private enum Status{ Unresolved, Resolving, Resolved } 
        /** Resolved if expression has been evaluated */
        protected Status status;
        /** Constructor if the constant value (and hence its type) is known */
        ConstantEntry(String id, Position p, Scope s, Type t, int val) {
            super( id, p, s, t, true );
            value = val;
            status = Status.Resolved;
        }
        /** Constructor when only an abstract syntax tree is available. */
        ConstantEntry(String id, Position p, Scope s, Type t, ConstExp val) {
            super( id, p, s, t, false );
            value  = 0x80808080;    // silly default value
            tree = val;
            status = Status.Unresolved;
        }
        /** Resolve references to constant identifiers and evaluate expression
         */
        @Override
        public void resolve() {
            switch ( status ) {
            case Unresolved:
                status = Status.Resolving;
                value = tree.getValue();
                type = tree.getType();
                status = Status.Resolved;
                resolved = true;
                break;
            case Resolving:
                error( "circular reference in constant expression", pos );
                status = Status.Resolved;
                resolved = true;
                break;
            case Resolved:
                break;
            }
        }
        public int getValue() {
            if( !resolved ) {
                resolve();
            }
            return value;
        }
        @Override
        public String toString() {
            return toString("CONST ", " : ") + " = " + value;
        }
    }

    /** Symbol table entry for a TYPE identifier */
    public static class TypeEntry extends SymEntry {

        TypeEntry( String id, Position p, Scope s, Type t ) {
            super( id, p, s, t, false );
        }
        @Override
        public String toString() {
            return toString("TYPE  ", " = ");
        }
    }

    /** Symbol table entry for a variable identifier */
    public static class VarEntry extends SymEntry {
        /** offset of variable starting from 0 */
        protected int offset;
        
        public VarEntry(String id, Position p, Scope s, ReferenceType t ) {
            super( id, p, s, t, false );
        }
        public ReferenceType getType() {
            return (ReferenceType)super.getType();
        }
        /** resolving a variable requires allocating space for it */
        @Override
        public void resolve() {
            if( ! resolved ) {
                // resolve the type of the variable
                super.resolve();
                /* Space is allocated for the variable and the address of that 
                 * location placed in the entry for the variable.
                 * The space allocated depends on the size of its type.
                 */
                Type baseType = ((Type.ReferenceType)type).getBaseType();
                offset = scope.allocVariableSpace( baseType.getSpace() );
            }
        }
        /** @requires resolved */
        public int getOffset() {
            assert resolved;
            return offset;
        }
        public void setOffset( int offset ) {
            this.offset = offset;
        }
        @Override
        public String toString() {
            return toString("VAR   ", " : ") + " offset " + offset;
        }
    }
    /** Symbol table entry for a parameter.
     * Note that ParamEntry extends VarEntry so that parameters are 
     * treated as local variables when they are referenced. */
    public static class ParamEntry extends VarEntry {
        /** result is false for a value parameter and true for a result parameter */
        boolean result;
        /** Constructor defaults to a value parameter */
        public ParamEntry(String id, Position p, Scope s, ReferenceType type){
            super( id, p, s, type );
        }
        /** Constructor for a value/result parameter
         * @param id name of the parameter
         * @param p position of declaration of parameter
         * @param s scope in which declared
         * @param type of parameter (must be ReferenceType)
         * @param result true if and only if this is a result parameter
         */
        public ParamEntry( String id, Position p, Scope s, ReferenceType type,
                boolean result ) {
            super( id, p, s, type );
            this.result = result;
        }
        /** @returns true if and only if this is a result parameter */
        public boolean isResultParam() {
            return result;
        }
        /** resolving a parameter's type - this version is the same as the
         * default for Type but not for VarEntry which is the super type
         * of  ParamEntry and hence we have to override it. */
        @Override
        public void resolve() {
            if( ! resolved ) {
                type = type.resolveType( pos );
                resolved = true;
            }
        }
        /** @param offset of the parameter from the frame pointer  
         * @requires offset <= 0 */
        @Override
        public void setOffset(int offset) {
            this.offset = offset;
        }
        /** @returns the space required for storing this parameter */
        public int getSpace() {
            return ((ReferenceType)getType()).getBaseType().getSpace();
        }
        @Override
        public String toString()
        {
            return 
                    (result ? "RESULT " : "VALUE ") +
                    "PARAM : " + " offset " + offset;
        }
    }


    /** Symbol table entry for a procedure identifier */
    public static class ProcedureEntry extends SymEntry {
        /** start location of the procedure code */
        private int start;
        /** Scope of entries declared locally to the procedure */
        private Scope localScope;

        public ProcedureEntry( String id, Position p, Scope s, 
                                  Type.ProcedureType type ) {
            super( id, p, s, type, false );
        } 
        public ProcedureEntry( String id, Position p, Scope s ) {
            this( id, p, s, new Type.ProcedureType() );
        }
        @Override
        public Type.ProcedureType getType() {
            return (Type.ProcedureType)type;
        }
        public Scope getLocalScope() {
            return localScope;
        }
        public void setLocalScope( Scope symtab ) {
            localScope = symtab;
        }
       public int getStart() {
            return start;
        }
        public void setStart( int start ) {
            this.start = start;
        }
        @Override
        public String toString() {
            return toString("PROC  ", " : ") + " start " + start;
        }
    }

    /** Symbol table entry for an operator */
    public static class OperatorEntry extends SymEntry {
        /** Operator entry constructor with single type */
        OperatorEntry(String id, Position p, Scope s, Type operatorType ) {
            super( id, p, s, operatorType, true );
        }
        /** Operator entry constructor with multiple types,
         * i.e. an overloaded operator.
         */
        OperatorEntry(String id, Position p, Scope s, Type... types ) {
            super( id, p, s, new Type.IntersectionType( types ), true );
        }
        /** Add an extra type for an operator. */ 
        public void extendType( Type operatorType ) {
            if (type instanceof Type.IntersectionType ) {
                /* Extend type by adding operatorType */
                ((Type.IntersectionType)type).addType( operatorType );
            } else {
                /* Convert type to intersection type containing both
                 * current type and operatorType.
                 */
                type = new Type.IntersectionType( type, operatorType );
            }
        }
        @Override
        public String toString() {
            return toString("OPER  ", " : ");
        }
    }

    private static void error( String message, Position pos ) {
        ErrorHandler.getErrorHandler().error(message, pos);
    }
}
