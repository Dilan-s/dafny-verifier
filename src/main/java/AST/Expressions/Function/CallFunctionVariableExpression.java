package AST.Expressions.Function;

import AST.Expressions.Variable.VariableExpression;
import AST.SymbolTable.Function.Function;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class CallFunctionVariableExpression extends CallFunctionExpression {

  public CallFunctionVariableExpression(SymbolTable symbolTable, Function function,
    VariableExpression var) {
    super(symbolTable, function, List.of(var));
    variables.add(var.getVariable());
  }

  @Override
  public String toString() {
    return String.format("%s(%s)", function.getName(), variables.stream()
      .map(Variable::getName)
      .collect(Collectors.joining(", ")));
  }

  @Override
  protected List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s,
    boolean unused) {
    List<Object> r = new ArrayList<>();

    List<Object> l = new ArrayList<>();
    for (Variable arg : variables) {
      List<Object> value = arg.getValue(paramsMap);
      for (Object v : value) {
        if (v == null) {
          r.add(null);
          return r;
        }
        l.add(v);
      }
    }
    return function.execute(variables, s);
  }

  @Override
  public boolean validForFunctionBody() {
    return false;
  }
}
