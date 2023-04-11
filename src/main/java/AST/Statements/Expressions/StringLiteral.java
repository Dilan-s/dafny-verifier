package AST.Statements.Expressions;

import AST.Errors.SemanticException;
import AST.Statements.Statement;
import AST.SymbolTable.Method;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Variable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class StringLiteral implements Expression {

    private final String value;
    private final Type type;
    private SymbolTable symbolTable;

    public StringLiteral(Type type, SymbolTable symbolTable, String value) {
        this.type = type;
        this.symbolTable = symbolTable;
        this.value = value;
    }

    @Override
    public List<Type> getTypes() {
        return List.of(type);
    }

    @Override
    public void semanticCheck(Method method) throws SemanticException {
    }

    @Override
    public String toString() {
        return String.format("\"%s\"", value);
    }

    @Override
    public int hashCode() {
        return Objects.hash(value);
    }

    @Override
    public boolean equals(Object obj) {
        if (!(obj instanceof StringLiteral)) {
            return false;
        }
        StringLiteral other = (StringLiteral) obj;
        return value.equals(other.value);
    }

    @Override
    public List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s) {
        List<Object> r = new ArrayList<>();
        r.add(value);
        return r;
    }

    @Override
    public List<Statement> expand() {
        return new ArrayList<>();
    }
}
