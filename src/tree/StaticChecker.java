package tree;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

import source.Errors;
import source.Position;
import syms.Predefined;
import syms.SymEntry;
import syms.SymbolTable;
import syms.Type;
import syms.Type.IncompatibleTypes;
import tree.DeclNode.DeclListNode;
import tree.ExpNode.ParamNode;
import tree.StatementNode.*;

/** class StaticSemantics - Performs the static semantic checks on
 * the abstract syntax tree using a visitor pattern to traverse the tree.
 * @version $Revision: 22 $  $Date: 2014-05-20 15:14:36 +1000 (Tue, 20 May 2014) $
 * See the notes on the static semantics of PL0 to understand the PL0
 * type system in detail.
 */
public class StaticChecker implements DeclVisitor, StatementVisitor, 
                                        ExpTransform<ExpNode> {

    /** The static checker maintains a symbol table reference.
     * Its current scope is that for the procedure 
     * currently being processed.
     */
    private SymbolTable symtab;
    /** Errors are reported through the error handler. */
    private Errors errors;

    /** Construct a static checker for PL0.
     * @param errors is the error message handler.
     */
    public StaticChecker( Errors errors ) {
        super();
        this.errors = errors;
    }
    /** The tree traversal starts with a call to visitProgramNode.
     * Then its descendants are visited using visit methods for each
     * node type, which are called using the visitor pattern "accept"
     * method (or "transform" for expression nodes) of the abstract
     * syntax tree node.
     */
    public void visitProgramNode(ProgramNode node) {
        // Set up the symbol table to be that for the main program.
        symtab = node.getBaseSymbolTable();
        // Set the current symbol table scope to that for the procedure.
        symtab.reenterScope( node.getBlock().getBlockLocals() );
        // resolve all references to identifiers with the declarations
        symtab.getCurrentScope().resolveScope();
        // Check the main program block.
        node.getBlock().accept( this );
        //System.out.println( node );
    }
    public void visitBlockNode(BlockNode node) {
        // Check the procedures, if any.
        node.getProcedures().accept( this );
        // Check the body of the block.
        node.getBody().accept( this );
        // System.out.println( symtab );
        // Restore the symbol table to the parent scope (not really necessary)
        symtab.leaveScope();
        //System.out.println( "Block Body\n" + node.getBody() );
    }
    public void visitDeclListNode(DeclListNode node) {
        for( DeclNode declaration : node.getDeclarations() ) {
            declaration.accept( this );
        }
    }
    /** Procedure, function or main program node */
    public void visitProcedureNode(DeclNode.ProcedureNode node) {
        SymEntry.ProcedureEntry procEntry = node.getProcEntry();
        // Set the current symbol table scope to that for the procedure.
        symtab.reenterScope( procEntry.getLocalScope() );
        // resolve all references to identifiers with the declarations
        symtab.getCurrentScope().resolveScope();
        // Check the block of the procedure.
        node.getBlock().accept( this );
    }
    /*************************************************
     *  Statement node static checker visit methods
     *************************************************/
    public void visitStatementErrorNode(StatementNode.ErrorNode node) {
        // Nothing to check - already invalid.
    }

    public void visitAssignmentNode(StatementNode.AssignmentNode node) {
        // Check the left side left value.
        ExpNode left = node.getVariable().transform( this );
        node.setVariable( left );
        // Check the right side expression.
        ExpNode exp = node.getExp().transform( this );
        node.setExp( exp );
        // Validate that it is a true left value and not a constant.
        Type lvalType = left.getType();
        if( ! (lvalType instanceof Type.ReferenceType) ) {
            if( lvalType != Type.ERROR_TYPE ) {
                errors.error( "variable (i.e., L-Value) expected", left.getPosition() );
            }
        } else {
            /* Validate that the right expression is assignment
             * compatible with the left value. This may require that the 
             * right side expression is coerced to the dereferenced
             * type of the left side LValue. */
            Type baseType = ((Type.ReferenceType)lvalType).getBaseType();
            node.setExp( baseType.coerceExp( exp ) );
        }
    }

    public void visitWriteNode(StatementNode.WriteNode node) {
        // Check the expression being written.
        ExpNode exp = node.getExp().transform( this );
        // coerce expression to be of type integer,
        // or complain if not possible.
        node.setExp( Predefined.INTEGER_TYPE.coerceExp( exp ) );
    }

    
    public void visitCallNode(StatementNode.CallNode node) {
        SymEntry.ProcedureEntry procEntry;
        Type.ProcedureType procType;
        // Look up the symbol table entry for the procedure.
        SymEntry entry = symtab.getCurrentScope().lookup( node.getId() );
        if( entry instanceof SymEntry.ProcedureEntry ) {
            procEntry = (SymEntry.ProcedureEntry)entry;
            node.setEntry( procEntry );
            procType = procEntry.getType();
        } else {
            errors.error( "Procedure identifier required", node.getPosition() );
            return;
        }
        // Check procType is a valid procedure type or not
        if(! isValidProcedure(procType)){ 
        	return;
        }
        List<SymEntry.ParamEntry> formalParamList = procType.getParams();
        List<ExpNode.ParamNode> actualParamList = node.getActualParamList();
        if(formalParamList.size() == actualParamList.size()) {
        	for(int i = 0; i < formalParamList.size(); i++) {
        		SymEntry.ParamEntry formalEntry = formalParamList.get(i);
        		ExpNode.ParamNode actualNode = actualParamList.get(i);
        		Type.ReferenceType refFormalType = formalEntry.getType();
        		Type baseFormalType = refFormalType.getBaseType();
        		ExpNode actualExp = actualNode.getExp().transform(this);
        		if(formalEntry.isResultParam()) { // is result parameter
        			actualNode.setResultParam(true);
        			Type refActualType = actualExp.getType();
        			if(refActualType instanceof Type.ReferenceType) {
        				/* Validate that the formal result parameter is assignment
        				 * compatible with the actual parameter. */
        				Type baseActualType = ((Type.ReferenceType)refActualType).getBaseType();
        				baseActualType.coerceExp(new ExpNode.VariableNode(actualNode.getPosition(), formalEntry));
        				actualNode.setExp(actualExp);
        				actualNode.setType((Type.ReferenceType) refActualType);
        			} else { // refActualType is not a type of Type.ReferenceType
        				if(refActualType != Type.ERROR_TYPE) {
        					errors.error("actual result parameter must be an LValue", actualExp.getPosition());
        				}
        			}
        		} else { // formalEntry is formal value parameter
        			/* Validate that the actual expression is assignment
        			 * compatible with the formal value parameter. 
        			 * This may require that the actual expression is coerced
        			 * to the dereferenced type of the formal value parameter. */
        			actualNode.setExp(baseFormalType.coerceExp(actualExp));
        			actualNode.setResultParam(false);
        		}
        	}
        } else {// number of actual parameters is not the same as that of formal parameters
        	errors.error("wrong number of parameters", node.getPosition());
        	return;
        }
    }
    
    /** Check whether a procedure is valid(No error when declared) or not
     * @return true if valid, otherwise false */
    private boolean isValidProcedure(Type.ProcedureType procType) {
    	List<SymEntry.ParamEntry> paramEntryList = procType.getParams();
    	for(SymEntry.ParamEntry paramEntry : paramEntryList) {
    		Type baseType = paramEntry.getType().getBaseType();
    		if(baseType == Type.ERROR_TYPE) {
    			return false;
    		}
    	}
    	return true;
    }

    public void visitStatementListNode( StatementNode.ListNode node ) {
        for( StatementNode s : node.getStatements() ) {
            s.accept( this );
        }
    }
    private ExpNode checkCondition( ExpNode cond ) {
        // Check and transform the condition
        cond = cond.transform( this );
        /* Validate that the condition is boolean, which may require
         * coercing the condition to be of type boolean. */     
        return Predefined.BOOLEAN_TYPE.coerceExp( cond );
    }
    public void visitIfNode(StatementNode.IfNode node) {
        // Check the condition.
        node.setCondition( checkCondition( node.getCondition() ) );
        // Check the 'then' part.
        node.getThenStmt().accept( this );
        // Check the 'else' part.
        node.getElseStmt().accept( this );
    }

    public void visitWhileNode(StatementNode.WhileNode node) {
        // Check the condition.
        node.setCondition( checkCondition( node.getCondition() ) );
        // Check the body of the loop.
        node.getLoopStmt().accept( this );
    }
    /*************************************************
     *  Expression node static checker visit methods
     *  The static checking visitor methods for expressions
     *  transform the expression to include resolve identifier
     *  nodes, and add nodes like dereference nodes, and
     *  narrow and widen subrange nodes.
     *  These ensure that the transformed tree is type consistent.
     *************************************************/
    public ExpNode visitErrorExpNode(ExpNode.ErrorNode node) {
        // Nothing to do - already invalid.
        return node;
    }

    public ExpNode visitConstNode(ExpNode.ConstNode node) {
        // type already set up
        return node;
    }
    /** Reads an integer value from input */
    public ExpNode visitReadNode(ExpNode.ReadNode node) {
        // type already set up
        return node;
    }
    /** Handles binary and unary operators, 
     * allowing the types of operators to be overloaded.
     */
    public ExpNode visitOperatorNode( ExpNode.OperatorNode node ) {
        /* Operators can be overloaded */
        /* Check the arguments to the operator */
        ExpNode arg = node.getArg().transform( this );
        /* Lookup the operator in the symbol table to get its type */
        Type opType = symtab.getCurrentScope().lookupOperator(node.getOp().getName()).getType();
        if( opType instanceof Type.FunctionType ) {
            /* The operator is not overloaded. Its type is represented
             * by a FunctionType from its argument's type to its
             * result type.
             */
            Type.FunctionType fType = (Type.FunctionType)opType;
            node.setArg( fType.getArgType().coerceExp( arg ) );
            node.setType( fType.getResultType() );
        } else if( opType instanceof Type.IntersectionType ) {
            for( Type t : ((Type.IntersectionType)opType).getTypes() ) {
                /* The operator is overloaded. Its type is represented
                 * by an IntersectionType containing a set of possible
                 * types for the operator, each of which is a FunctionType.
                 * Each possible type is tried until one succeeds.
                 */
                Type.FunctionType fType = (Type.FunctionType)t;
                Type opArgType = fType.getArgType();
                try {
                    /* Coerce the argument to the argument type for 
                     * this operator type. If the coercion fails an
                     * exception will be trapped and an alternative 
                     * function type within the intersection tried.
                     */
                    ExpNode newArg = opArgType.coerceToType( arg );
                    /* The coercion succeeded if we get here */
                    node.setArg( newArg );
                    node.setType( fType.getResultType() );
                    return node;
                } catch ( IncompatibleTypes ex ) {
                    // Allow "for" loop to try an alternative
                }
            }
            // no match in intersection type
            errors.error( "Type of argument " + arg.getType() + 
                    " does not match " + opType, node.getPosition() );
            node.setType( Type.ERROR_TYPE );
        } else {
            errors.fatal( "Invalid operator type", node.getPosition() );
        }
        return node;
    }
    /** An ArgumentsNode is used to represent a list of arguments, each 
     * of which is an expression. The arguments for a binary operator are 
     * represented by list with two elements.
     */
    public ExpNode visitArgumentsNode( ExpNode.ArgumentsNode node ) {
        List<ExpNode> newExps = new LinkedList<ExpNode>();
        List<Type> types = new LinkedList<Type>();
        for( ExpNode exp : node.getArgs() ) {
            ExpNode newExp = exp.transform( this );
            newExps.add( newExp );
            types.add( newExp.getType() );
        }
        node.setArgs( newExps );
        node.setType( new Type.ProductType( types ) );
        return node;
    }
    /** A DereferenceNode allows a variable (of type ref(int) say) to be
     * dereferenced to get its value (of type int). 
     */
    public ExpNode visitDereferenceNode(ExpNode.DereferenceNode node) {
        // Check the left value referred to by this dereference node
        ExpNode lVal = node.getLeftValue().transform( this );
        node.setLeftValue( lVal );
        /* The type of the dereference node is the base type of its 
         * left value. */
        Type lValueType = lVal.getType();
        if( lValueType instanceof Type.ReferenceType ) {
            node.setType( lValueType.optDereferenceType() ); // not optional here
        } else if( lValueType != Type.ERROR_TYPE ) { // avoid cascading errors
            errors.error( "cannot dereference an expression which isn't a reference",
                    node.getPosition() );
        }
        return node;
    }
    /** When parsing an identifier within an expression one can't tell
     * whether it has been declared as a constant or an identifier.
     * Here we check which it is and return either a constant or 
     * a variable node.
     */
    public ExpNode visitIdentifierNode(ExpNode.IdentifierNode node) {
        // First we look up the identifier in the symbol table.
        ExpNode newNode;
        SymEntry entry = symtab.getCurrentScope().lookup( node.getId() );
        if( entry instanceof SymEntry.ConstantEntry ) {
            // Set up a new node which is a constant.
            SymEntry.ConstantEntry constEntry = 
                (SymEntry.ConstantEntry)entry;
            newNode = new ExpNode.ConstNode( node.getPosition(), 
                    constEntry.getType(), constEntry.getValue() );
        } else if( entry instanceof SymEntry.VarEntry ) {
            // Set up a new node which is a variable.
            SymEntry.VarEntry varEntry = (SymEntry.VarEntry)entry;
            newNode = new ExpNode.VariableNode(node.getPosition(), varEntry);
        } else {
            // Undefined identifier or a type or procedure identifier.
            // Set up new node to be an error node.
            newNode = new ExpNode.ErrorNode( node.getPosition() );
            errors.error("Constant or variable identifier required", node.getPosition() );
        }
        return newNode;
    }

    public ExpNode visitVariableNode(ExpNode.VariableNode node) {
        // Type already set up
        return node;
    }
    public ExpNode visitNarrowSubrangeNode(ExpNode.NarrowSubrangeNode node) {
        // Nothing to do.
        return node;
    }

    public ExpNode visitWidenSubrangeNode(ExpNode.WidenSubrangeNode node) {
        // Nothing to do.
        return node;
    }
	@Override
	public ExpNode visitParamNode(ParamNode node) {
		return node;
	}

}
