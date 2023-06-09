package AST.Expressions;

import AST.Generator.VariableNameGenerator;
import AST.Statements.AssignmentStatement;
import AST.Statements.Statement;
import AST.SymbolTable.Method;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class CallMethodExpression extends BaseExpression {

    private SymbolTable symbolTable;
    private Method method;
    private List<Variable> variables;
    private List<Statement> assignments;
    private List<Variable> assignedVariables;
    private CallMethod callExpr;
    private AssignmentStatement assignStat;

    private List<List<Statement>> expanded;

    public CallMethodExpression(SymbolTable symbolTable, Method method, List<Expression> args) {
        super();
        this.symbolTable = symbolTable;
        this.method = method;
        this.variables = new ArrayList<>();
        this.assignments = new ArrayList<>();
        this.assignedVariables = new ArrayList<>();
        addArg(args);
        generateReturnAssignment();

        this.expanded = new ArrayList<>();
        assignments.forEach(s -> expanded.add(s.expand()));
        expanded.add(List.of(assignStat));
    }

    private void addArg(List<Expression> expressions) {
        for (Expression e : expressions) {
            addArg(e);
        }
    }

    private void addArg(Expression expression) {
        Type type = expression.getTypes().get(0);
        String var = VariableNameGenerator.generateVariableValueName(type, symbolTable);
        Variable variable = new Variable(var, type);
        variables.add(variable);

        AssignmentStatement stat = new AssignmentStatement(symbolTable, List.of(variable), expression);
        assignments.add(stat);
    }


    private void generateReturnAssignment() {
        assignedVariables = new ArrayList<>();

        for (Type returnType : method.getReturnTypes()) {
            Type rt = returnType.concrete(symbolTable);
            String var = VariableNameGenerator.generateVariableValueName(rt, symbolTable);
            Variable variable = new Variable(var, rt);
            assignedVariables.add(variable);
        }

        callExpr = new CallMethod(method, variables);

        assignStat = new AssignmentStatement(symbolTable, assignedVariables, callExpr);
    }

    @Override
    public List<Type> getTypes() {
        return method.getReturnTypes();
    }

    @Override
    public List<Statement> expand() {
        int i;
        for (i = 0; i < assignments.size(); i++) {
            Statement assignment = assignments.get(i);
            if (assignment.requireUpdate()) {
                expanded.set(i, assignment.expand());
            }
        }
        if (assignStat.requireUpdate()) {
            expanded.set(i, assignStat.expand());
        }
        return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
    }

    @Override
    public boolean requireUpdate() {
        return assignments.stream().anyMatch(Statement::requireUpdate) || assignStat.requireUpdate();
    }

    @Override
    public boolean isValidReturn() {
        return false;
    }

    @Override
    public String toString() {
        return assignedVariables.stream()
            .map(Variable::getName)
            .collect(Collectors.joining(", "));
    }

    @Override
    protected List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s, boolean unused) {
        return assignedVariables.stream()
            .map(v -> v.getValue(paramsMap))
            .flatMap(Collection::stream)
            .collect(Collectors.toList());
    }

    @Override
    public boolean validForFunction() {
        return true;
    }

    private class CallMethod extends BaseExpression {

        private Method method;
        private List<Variable> args;

        public CallMethod(Method method, List<Variable> args) {
            super();
            this.method = method;
            this.args = args;
        }

        @Override
        public List<Type> getTypes() {
            return method.getReturnTypes();
        }

        @Override
        public String toString() {
            return String.format("%s(%s)", method.getName(), args.stream()
                .map(Variable::getName)
                .collect(Collectors.joining(", ")));
        }

        @Override
        public List<Statement> expand() {
            return new ArrayList<>();
        }

        @Override
        public boolean requireUpdate() {
            return true;
        }

        @Override
        public List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s, boolean unused) {
            List<Object> r = new ArrayList<>();

            List<Object> l = new ArrayList<>();
            for (Variable arg : args) {
                List<Object> value = arg.getValue(paramsMap);
                for (Object v : value) {
                    if (v == null) {
                        method.getReturnTypes().forEach(t -> r.add(null));
                        return r;
                    }
                    l.add(v);
                }
            }
            return method.execute(args, s);
        }

        @Override
        public boolean validForFunction() {
            return true;
        }
    }
}
