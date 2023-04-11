package AST.Statements;

import AST.Errors.SemanticException;
import AST.Statements.Expressions.Expression;
import AST.Statements.util.ReturnStatus;
import AST.SymbolTable.Method;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Variable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class AssignmentStatement implements Statement {

    private final SymbolTable symbolTable;
    private final List<Variable> variables;
    private final List<Expression> values;
    private boolean declared;

    public AssignmentStatement(SymbolTable symbolTable, List<Variable> variables, List<Expression> values) {
        this.symbolTable = symbolTable;
        this.variables = variables;
        this.values = values;
        declared = variables.stream().allMatch(Variable::isDeclared);
        declareVariables();
    }

    public AssignmentStatement(SymbolTable symbolTable, List<Variable> variables, Expression value) {
        this(symbolTable, variables, List.of(value));
    }

    private void declareVariables() {
        for (int i = 0, variablesSize = variables.size(); i < variablesSize; i++) {
            Variable v = variables.get(i);
            v.setDeclared();
            symbolTable.addVariable(v);
        }

        List<Object> expValues = new ArrayList<>();
        for (Expression value : values) {
            List<Object> expressionValue = value.getValue();
            for (Object object : expressionValue) {
                expValues.add(object);
            }
        }

        for (int i = 0; i < variables.size(); i++) {
            Object expV = expValues.get(i);
            Variable v = variables.get(i);
            v.setValue(expV);
        }
    }

    @Override
    public void semanticCheck(Method method) throws SemanticException {
        List<Type> assignmentTypes = variables.stream().map(Variable::getType)
            .collect(Collectors.toList());

        List<Type> valueTypes = values.stream()
            .map(Expression::getTypes)
            .flatMap(Collection::stream)
            .collect(Collectors.toList());

        if (valueTypes.size() > 1
            && values.stream()
            .map(Expression::getTypes)
            .anyMatch(x -> x.size() > 1)) {
            throw new SemanticException(
                "If more than 1 expression given, then they must all be 1 valued");
        }

        int noValues = valueTypes.size();
        int noAssignTypes = assignmentTypes.size();
        if (noValues != noAssignTypes) {
            throw new SemanticException(String.format(
                "Expected %d arguments but actually got %d arguments in return statement",
                noAssignTypes, noValues));
        }

        for (int i = 0; i < noValues; i++) {
            Type expressionType = valueTypes.get(i);
            Type assignType = assignmentTypes.get(i);

            if (!assignType.equals(expressionType)) {
                throw new SemanticException(
                    String.format("Expected %dth argument to be %s but actually go %s", i,
                        assignType.getName(), expressionType.getName()));
            }
        }

        for (Expression e : values) {
            e.semanticCheck(method);
        }
    }

    @Override
    public String toString() {
        String rhs = values.stream()
            .map(Expression::toString)
            .collect(Collectors.joining(", "));
        if (declared) {
            String lhs = variables.stream()
                .map(Variable::getName)
                .collect(Collectors.joining(", "));

            return String.format("%s := %s;", lhs, rhs);
        } else {
            String lhs = variables.stream()
                .map(Variable::toString)
                .collect(Collectors.joining(", "));


            return String.format("var %s := %s;", lhs, rhs);
        }
    }

    @Override
    public ReturnStatus assignReturnIfPossible(Method method, ReturnStatus currStatus, List<Expression> dependencies) {
        return currStatus;
    }

    @Override
    public List<Object> execute(Map<Variable, Variable> paramMap, StringBuilder s) {
        List<Object> expValues = new ArrayList<>();
        for (Expression value : values) {
            List<Object> expressionValue = value.getValue(paramMap, s);
            for (Object object : expressionValue) {
                expValues.add(object);
            }
        }

        for (int i = 0; i < variables.size(); i++) {
            Object expV = expValues.get(i);
            Variable v = variables.get(i);
            v.setValue(expV);
        }
        return null;
    }

    @Override
    public List<Statement> expand() {
        List<Statement> r = new ArrayList<>();
        List<Statement> list = new ArrayList<>();
        for (Expression value : values) {
            List<Statement> expand = value.expand();
            for (Statement statement : expand) {
                list.add(statement);
            }
        }
        r.addAll(list);
        r.add(this);
        return r;
    }
}
