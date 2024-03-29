package AST.Expressions.Method;

import AST.Expressions.BaseExpression;
import AST.Expressions.Expression;
import AST.Generator.VariableNameGenerator;
import AST.Statements.AssignmentStatement;
import AST.Statements.Statement;
import AST.SymbolTable.Method.Method;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.UserDefinedTypes.DClass;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class CallClassMethodExpression extends CallMethodExpression {

  private final Expression classExpression;
  private final Variable classVariable;
  private final AssignmentStatement classAssign;

  public CallClassMethodExpression(SymbolTable symbolTable, Method method,
    Expression classExpression, List<Expression> args) {
    super(symbolTable, method, args);
    this.classExpression = classExpression;
    DClass dClass = classExpression.getTypes().get(0).asDClass();

    this.classVariable = new Variable(
      VariableNameGenerator.generateVariableValueName(dClass, symbolTable), dClass);
    this.classAssign = new AssignmentStatement(symbolTable, List.of(classVariable),
      classExpression);

    expanded.add(assignments.size(), classAssign.expand());
  }

  @Override
  public List<Statement> expand() {
    int i;
    for (i = 0; i < assignments.size(); i++) {
      Statement assignment = assignments.get(i);
      expanded.set(i, assignment.expand());
    }
    expanded.set(i, classAssign.expand());
    i++;
    expanded.set(i, assignStat.expand());
    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  protected Expression getCallExpression() {
    return new CallMethod(method, variables);
  }

  private class CallMethod extends BaseExpression {

    private final Method method;
    private final List<Variable> args;

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
      return String.format("%s.%s(%s)", classVariable.getName(), method.getName(), args.stream()
        .map(Variable::getName)
        .collect(Collectors.joining(", ")));
    }

    @Override
    public List<Statement> expand() {
      return new ArrayList<>();
    }

    @Override
    protected List<Object> getValue(Map<Variable, Variable> paramMap, StringBuilder s,
      boolean unused) {
      method.assignThis(classVariable);
      List<Object> r = new ArrayList<>();

      List<Object> l = new ArrayList<>();
      for (Variable arg : args) {
        List<Object> value = arg.getValue(paramMap);
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
  }


}
