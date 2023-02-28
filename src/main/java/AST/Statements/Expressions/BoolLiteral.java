package AST.Statements.Expressions;

import AST.Errors.SemanticException;
import AST.SymbolTable.Method;
import AST.SymbolTable.PrimitiveTypes.Bool;
import AST.SymbolTable.SymbolTable;
import AST.SymbolTable.Type;
import java.util.List;

public class BoolLiteral implements Expression {

    private final boolean value;
    private SymbolTable symbolTable;

    public BoolLiteral(boolean value) {
        this.value = value;
    }

    @Override
    public List<Type> getTypes() {
        return List.of(new Bool());
    }

    @Override
    public void semanticCheck(Method method) throws SemanticException {
    }

    @Override
    public void setSymbolTable(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    @Override
    public String toString() {
        return String.valueOf(value);
    }
}