package syms;

import java.util.Collection;
import java.util.TreeMap;
import java.util.SortedMap;

import machine.StackMachine;
import source.Position;
import syms.SymEntry;
import syms.SymEntry.ProcedureEntry;
import syms.Type.ReferenceType;
import tree.ConstExp;
import tree.StatementNode;

/** A Scope represents a static scope for a procedure, main program or 
 * the predefined scope. 
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 * It provides operations to add and look up identifiers. 
 * Searching for an identifier in a scope starts at the current scope, 
 * but then if it is not found, the search proceeds to the next outer 
 * (parent) scope, and so on. 
 */
public class Scope {
    /** Parent Scope */
    private Scope parent;
    /** Static level of this scope */
    private int level;
    /** Symbol table entry for the procedure that owns this scope */
    private ProcedureEntry procEntry;
    /** Symbol table entries. A SortedMap is used to avoid issues with 
     * hashing functions working differently on different implementations. 
     * This only affects minor things like the order of dumping symbol 
     * tables in trace backs. A Map/HashMap would still give a valid 
     * implementation. */
    private SortedMap<String, SymEntry> entries;
    /** space allocated for local variables within this scope */
    private int variableSpace;
    /** space allocated for parameters within this scope */
    private int paramValueSpace;
    /** space allocated for result parameters */
    private int resultParamSpace;
    /** space allocated for both value and result parameters */
    private int allParamSpace;


    /** This constructs a single scope within a symbol table
     * that is linked to the parent scope, which may be null to
     * indicate that there is no parent. 
     * @param parent scope
     * @param level of nesting of scope
     * @param procEntry the corresponding procedure's symbol table entry
     */
    public Scope( Scope parent, int level, ProcedureEntry procEntry ) {
        this.parent = parent;
        this.level = level;
        this.procEntry = procEntry;
        /* Initially empty */
        this.entries = new TreeMap<String, SymEntry>();
        variableSpace = 0;
        paramValueSpace = 0;
        resultParamSpace = 0;
        allParamSpace = 0;
    }
    public Scope getParent() {
        return parent;
    }
    public int getLevel() {
        return level;
    }
    public ProcedureEntry getProcEntry() {
        return procEntry;
    }
    /** @return the set of entries in this scope */
    public Collection<SymEntry> getEntries() {
        return entries.values();
    }
    /** Lookup id starting in the current scope and 
     * thence in the parent scope and so on.
     * @param id identifier to search for.
     * @return symbol table entry for the id, or null if not found.
     */
    public SymEntry lookup( String id ) {
        /** Lookup the entry in the current scope */
        SymEntry entry = entries.get( id ) ;
        if( entry == null && parent != null ) {
            /** If the entry is not in the current scope 
             * look it up in the parent scope, if there is one.
             */
            return parent.lookup( id );
        }
        return entry;
    }
    /** Add an entry to the scope unless an entry for the same name exists.
     * @param entry to be added
     * @return the entry added or null is it already exited in this scope. 
     */
    public SymEntry addEntry( SymEntry entry ) {
        if( entries.containsKey( entry.getIdent() ) ) {
            return null;
        } else {
            entries.put( entry.getIdent(), entry );
            return entry;
        }
    }
    /** Resolve references to type identifiers and allocate space 
     * for variables and check for circularly defined types and constants. */
    public void resolveScope() {
        for( SymEntry entry : entries.values() ) {
            // System.out.println( "Symtab resolving " + entry.ident );
            entry.resolve();
            // System.out.println( "Resolved entry " + entry );
        }
        //System.out.println( currentScope );
    }
    /** @return the amount of space allocated to local variables
     * within the current scope. */
    public int getVariableSpace() {
            return variableSpace;
    }
    /** Allocate space for a local variable.
     * @param size is the amount of space required for the variable.
     * @return address (offset) of allocated space */
    public int allocVariableSpace( int size ) {
            int base = variableSpace;
            variableSpace += size;
            return StackMachine.LOCALS_BASE + base;
    }
    /** @return the amount of space allocated to value parameters 
     * within the current scope. */
    public int getValueParameterSpace() {
        return paramValueSpace;
    }
    /** Allocate space for a parameter.
     * @param size is the amount of space required for the variable.
     * @return the address (offset) of the allocated space.
     * Offsets for parameters are assumed to be negative with respect 
     * to the frame pointer. */
    public int allocValueParameterSpace( int size ) {
        allParamSpace += size;
        paramValueSpace += size;
        return StackMachine.PARAMS_BASE - paramValueSpace;
    }
    /** @return the amount of space allocated to result parameters 
     * within the current scope. */
    public int getResultParameterSpace() {
        return resultParamSpace;
    }
    /** Allocate space for a result parameter.
     * It is assumed that result parameters are allocated after value
     * parameters.
     * @param size is the amount of space required for the result parameter.
     * @return the address (offset) of the allocated space.
     * Offsets for parameters are assumed to be negative with respect 
     * to the frame pointer. */
    public int allocResultParameterSpace( int size ) {
        resultParamSpace += size;
        allParamSpace += size;
        return StackMachine.PARAMS_BASE - allParamSpace;
    }
    
    /** Add a CONSTANT entry to the current scope - known value
     * @return a reference to the new entry unless an entry with the same name
     *         already exists in the current scope, in which case return null.
     */
    public SymEntry.ConstantEntry addConstant(String name, Position posn,
            Type type, int val) {
        SymEntry.ConstantEntry entry = 
            new SymEntry.ConstantEntry(name, posn, this, type, val);
        return (SymEntry.ConstantEntry) addEntry(entry);
    }
    /** Add a CONSTANT entry to the current scope - tree to be evaluated later
     * @return a reference to the new entry unless an entry with the same name
     *         already exists in the current scope, in which case return null.
     */
    public SymEntry.ConstantEntry addConstant(String name, Position posn,
            ConstExp val) {
        SymEntry.ConstantEntry entry =
            new SymEntry.ConstantEntry(name, posn, this, 
                Type.ERROR_TYPE, val);
        return (SymEntry.ConstantEntry) addEntry(entry);
    }
    /** Lookup a CONSTANT entry in all scopes starting from the current scope.
     * @param name of the CONSTANT to be looked up
     * @return entry for name if one is found and it is a CONSTANT entry 
     *         otherwise return null; note that a non-CONSTANT entry may mask
     *         a CONSTANT entry of the same name in an outer scope.
     */
    public SymEntry.ConstantEntry lookupConstant(String name) {
        SymEntry entry = lookup(name);
        if (entry == null || !(entry instanceof SymEntry.ConstantEntry)) {
            return null;
        }
        return (SymEntry.ConstantEntry) entry;
    }
    /** Add a TYPE entry to the current scope 
     * @return a reference to the new entry unless an entry with the same name
     *         already exists in the current scope, in which case return null.
     */
    public SymEntry.TypeEntry addType(String name, Position posn, Type type) {
        SymEntry.TypeEntry entry =
                new SymEntry.TypeEntry(name, posn, this, type);
        return (SymEntry.TypeEntry) addEntry(entry);
    }
    /** Lookup a TYPE entry in all scopes starting from the current scope. 
     * @param name of the TYPE to be looked up
     * @return entry for name if one is found and it is a TYPE entry 
     *         otherwise return null; note that a non-TYPE entry may mask
     *         a TYPE entry of the same name in an outer scope.
     */
    public SymEntry.TypeEntry lookupType(String name) {
        SymEntry entry = lookup(name);
        if (entry == null || !(entry instanceof SymEntry.TypeEntry)) {
            return null;
        }
        return (SymEntry.TypeEntry) entry;
    }
    /** Add a VARIABLE entry to the current scope.
     * @return a reference to the new entry unless an entry with the same name
     *         already exists in the current scope, in which case return null.
     */
    public SymEntry.VarEntry addVariable(String name, Position posn, 
            ReferenceType type){
        SymEntry.VarEntry entry =
                new SymEntry.VarEntry(name, posn, this, type );
        return (SymEntry.VarEntry) addEntry(entry);
    }
    /** Lookup a VARIABLE entry in all scopes starting from the current scope.
     * @param name of the VARIABLE to be looked up
     * @return entry for name if one is found and it is a VARIABLE entry 
     *         otherwise return null; note that a non-VARIABLE entry may mask
     *         a VARIABLE entry of the same name in an outer scope.
     */
    public SymEntry.VarEntry lookupVariable(String name) {
        SymEntry entry = lookup(name);
        if (entry == null || !(entry instanceof SymEntry.VarEntry)) {
            return null;
        }
        return (SymEntry.VarEntry) entry;
    }
    /** Add a PROCEDURE entry to the current scope
     * @return a reference to the new entry unless an entry with the same name
     *         already exists in the current scope, in which case return null.
     */
    public SymEntry.ProcedureEntry addProcedure(String name, Position posn) {
        SymEntry.ProcedureEntry entry =
                new SymEntry.ProcedureEntry(name, posn, this );
        return (SymEntry.ProcedureEntry) addEntry(entry);
    }
    public SymEntry.ProcedureEntry addProcedure(String name, Position posn,
            Type.ProcedureType type ) {
        SymEntry.ProcedureEntry entry =
                new SymEntry.ProcedureEntry(name, posn, this, type );
        return (SymEntry.ProcedureEntry) addEntry(entry);
    }
    /** Lookup a PROCEDURE entry in all scopes starting from the current scope.
     * @param name of the PROCEDURE to be looked up
     * @return entry for name if one is found and it is a PROCEDURE entry 
     *         otherwise return null; note that a non-PROCEDURE entry may mask
     *         a PROCEDURE entry of the same name in an outer scope.
     */
    public SymEntry.ProcedureEntry lookupProcedure(String name) {
        SymEntry entry = lookup(name);
        if (entry == null || !(entry instanceof SymEntry.ProcedureEntry)) {
            return null;
        }
        return (SymEntry.ProcedureEntry) entry;
    }
    /** Add an OPERATOR entry to the current scope
     * @return a reference to the new entry unless an entry with the same name
     *         already exists in the current scope, in which case return null.
     */
    public SymEntry.OperatorEntry addOperator(String name, Position posn,
            Type type ) {
        SymEntry.OperatorEntry entry = lookupOperator( name );
        if( entry == null ) {
            /** Create a new entry for the operator */
            entry = new SymEntry.OperatorEntry(name, posn, this, type );
            return (SymEntry.OperatorEntry) addEntry(entry);
        } else if( entry.getLevel() == getLevel() ) {
            /** Already defined at the current level - extend intersection type */
            entry.extendType( type );
            return entry;
        } else {
            /** Defined at an outer level create new entry with old
             * intersection type and extend with new type.
             */
            entry = new SymEntry.OperatorEntry(name, posn, this, 
                    entry.getType() );
            entry.extendType( type );
            return (SymEntry.OperatorEntry) addEntry(entry);
        }
    }
    /** Lookup an OPERATOR entry in all scopes starting from the current scope.
     * @param name of the OPERATOR to be looked up
     * @return entry for name if one is found and it is an OPERATOR entry 
     *         otherwise return null; note that a non-OPERATOR entry may mask
     *         a OPERATOR entry of the same name in an outer scope.
     */
    public SymEntry.OperatorEntry lookupOperator(String name) {
        SymEntry entry = lookup(name);
        if (entry == null || !(entry instanceof SymEntry.OperatorEntry)) {
            return null;
        }
        return (SymEntry.OperatorEntry) entry;
    }

    /* Dump contents of this scope */
    @Override
    public String toString() {
        String s = "Level " + level + " " + procEntry.getIdent();
        for( SymEntry entry : entries.values() ) {
            s += StatementNode.newLine(level) + entry;
        }
        return s;
    }
}
