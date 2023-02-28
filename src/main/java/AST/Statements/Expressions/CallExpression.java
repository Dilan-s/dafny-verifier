package AST.Statements.Expressions;

import AST.Errors.InvalidArgumentException;
import AST.Errors.SemanticException;
import AST.Generator.VariableNameGenerator;
import AST.Statements.AssignmentStatement;
import AST.Statements.Statement;
import AST.SymbolTable.Method;
import AST.SymbolTable.SymbolTable;
import AST.SymbolTable.Type;
import AST.SymbolTable.Variable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Collectors;

public class CallExpression implements Expression {

    private SymbolTable symbolTable;
    private final Method method;
    private final List<Variable> variables;
    private final List<Statement> assignments;
    private final List<VariableExpression> createdVariables;

    public CallExpression(Method method) {
        this.method = method;
        this.createdVariables = new ArrayList<>();
        this.variables = new ArrayList<>();
        this.assignments = new ArrayList<>();
    }

    public void addArg(Expression expression) throws InvalidArgumentException {

        if (expression.getTypes().size() != 1) {
            throw new InvalidArgumentException("Cannot add argument with more than 1 return value");
        }

        Type type = expression.getTypes().get(0);
        String var = VariableNameGenerator.generateVariableValueName(type);
        Variable variable = new Variable(var, type);
        variables.add(variable);

        AssignmentStatement stat = new AssignmentStatement(symbolTable);
        stat.addAssignment(List.of(variable), expression);
        stat.addAssignmentsToSymbolTable();

        assignments.add(stat);
    }


    @Override
    public List<Type> getTypes() {
        return method.getReturnTypes();
    }

    @Override
    public void semanticCheck(Method method) throws SemanticException {
        List<Type> methodTypes = method.getArgTypes();

        if (methodTypes.size() != variables.size()) {
            throw new SemanticException(
                String.format("Expected %d arguments but got %d arguments to method %s",
                    methodTypes.size(), variables.size(), method.getName()));
        }

        for (int i = 0; i < methodTypes.size(); i++) {
            Type methodType = methodTypes.get(i);
            Type varType = variables.get(i).getType();

            if (!methodType.isSameType(varType)) {
                throw new SemanticException(
                    String.format("Expected %dth argument to be %s, but actually was %s type", i,
                        methodType.getName(), varType.getName()));
            }
        }

    }

    @Override
    public List<String> toCode() {
        AssignmentStatement stat = new AssignmentStatement(symbolTable);
        List<Variable> assignedVariables = new ArrayList<>();
        for (Type returnType : method.getReturnTypes()) {
            String var = VariableNameGenerator.generateVariableValueName(returnType);
            Variable variable = new Variable(var, returnType);
            assignedVariables.add(variable);
            createdVariables.add(new VariableExpression(variable));
            symbolTable.addVariable(variable);
        }

        stat.addAssignment(assignedVariables, new CallMethodExpression(method, variables));

        assignments.add(stat);

        return assignments.stream()
            .map(Statement::toCode)
            .flatMap(Collection::stream)
            .collect(Collectors.toList());
    }

    @Override
    public void setSymbolTable(SymbolTable symbolTable) {
        this.symbolTable = symbolTable;
    }

    @Override
    public boolean isValidReturn() {
        return false;
    }

    @Override
    public String toString() {
        return createdVariables.stream()
            .map(VariableExpression::toString)
            .collect(Collectors.joining(", "));
    }


    private static class CallMethodExpression implements Expression {

        private Method method;
        private List<Variable> args;

        public CallMethodExpression(Method method, List<Variable> args) {
            this.method = method;
            this.args = args;
        }

        @Override
        public List<Type> getTypes() {
            return method.getReturnTypes();
        }

        @Override
        public void semanticCheck(Method method) throws SemanticException {

        }

        @Override
        public void setSymbolTable(SymbolTable symbolTable) {
        }

        @Override
        public String toString() {
            return String.format("%s(%s)", method.getName(), args.stream()
                .map(Variable::getName)
                .collect(Collectors.joining(", ")));
        }
    }
}