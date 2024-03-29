package AST.Expressions.Match;

import AST.Expressions.BaseExpression;
import AST.Expressions.Expression;
import AST.Generator.GeneratorConfig;
import AST.Statements.Statement;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class MatchExpressionCase extends BaseExpression {

  private final SymbolTable symbolTable;
  private final Type type;
  private final Expression test;
  private final Expression value;

  private final List<List<Statement>> expanded;

  public MatchExpressionCase(SymbolTable symbolTable, Type type, Expression test,
    Expression value) {
    super();
    this.symbolTable = symbolTable;
    this.type = type;
    this.test = test;
    this.value = value;

    this.expanded = new ArrayList<>();
    expanded.add(value.expand());

    expanded.add(test == null ? new ArrayList<>() : test.expand());
  }

  public MatchExpressionCase(SymbolTable symbolTable, Type type, Expression value) {
    this(symbolTable, type, null, value);
  }

  public Expression getTest() {
    return test;
  }

  @Override
  public List<Type> getTypes() {
    return List.of(type);
  }

  public Expression getValueExp() {
    return value;
  }

  @Override
  protected List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s,
    boolean unused) {
    return value.getValue(paramsMap, s);
  }

  @Override
  public List<Statement> expand() {
    expanded.set(0, value.expand());
    expanded.set(1, test == null ? new ArrayList<>() : test.expand());
    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  public boolean validForFunctionBody() {
    return super.validForFunctionBody() && (test == null || test.validForFunctionBody())
      && value.validForFunctionBody();
  }


  @Override
  public List<String> toOutput() {
    Set<String> res = new HashSet<>();

    List<String> ts = test == null ? List.of("_") : test.toOutput();
    for (String t : ts) {
      for (String v : value.toOutput()) {
        res.add(String.format("case %s => %s", t, v));
      }
    }

    List<String> r = new ArrayList<>(res);
    Collections.shuffle(r, GeneratorConfig.getRandom());
    return r.subList(0, Math.min(5, r.size()));
  }

  @Override
  public String toString() {
    return String.format("case %s => %s", test == null ? "_" : test.toString(), value.toString());
  }

  @Override
  public String minimizedTestCase() {
    return String.format("case %s => %s", test == null ? "_" : test.minimizedTestCase(),
      value.minimizedTestCase());
  }
}
