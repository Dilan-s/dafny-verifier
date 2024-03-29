package AST.Expressions.DSeq;

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

public class SeqLiteral extends BaseExpression {

  private final List<Expression> values;
  private Type type;
  private final SymbolTable symbolTable;

  private final List<List<Statement>> expanded;

  public SeqLiteral(SymbolTable symbolTable, Type type, List<Expression> values) {
    super();
    this.symbolTable = symbolTable;
    this.type = type;
    this.values = values;

    this.expanded = new ArrayList<>();
    values.forEach(v -> expanded.add(v.expand()));
  }

  @Override
  public List<Type> getTypes() {
    return List.of(type);
  }

  @Override
  public void setType(List<Type> types) {
    type = types.get(0);
  }

  @Override
  public String toString() {
    String value = values.stream()
      .map(Expression::toString)
      .collect(Collectors.joining(", "));
    return String.format("[%s]", value);
  }

  @Override
  public String minimizedTestCase() {
    String value = values.stream()
      .map(Expression::minimizedTestCase)
      .collect(Collectors.joining(", "));
    return String.format("[%s]", value);
  }

  @Override
  public List<String> toOutput() {
    Set<String> res = new HashSet<>();
    List<String> temp = new ArrayList<>();

    res.add("[");

    boolean first = true;
    for (Expression exp : values) {
      List<String> expOptions = exp.toOutput();
      temp = new ArrayList<>();
      for (String f : res) {
        for (String expOption : expOptions) {
          if (!first) {
            expOption = ", " + expOption;
          }
          String curr = f + expOption;
          temp.add(curr);
        }
      }
      if (expOptions.isEmpty()) {
        temp.addAll(res);
      }
      first = false;
      Collections.shuffle(temp, GeneratorConfig.getRandom());
      temp = temp.subList(0, Math.min(5, temp.size()));
      res = new HashSet<>(temp);
    }

    temp = new ArrayList<>();
    for (String f : res) {
      temp.add(f + "]");
    }
    res = new HashSet<>(temp);

    List<String> r = new ArrayList<>(res);
    Collections.shuffle(r, GeneratorConfig.getRandom());
    return r.subList(0, Math.min(5, res.size()));
  }

  @Override
  protected List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s,
    boolean unused) {
    List<Object> r = new ArrayList<>();

    List<Object> l = new ArrayList<>();
    for (Expression exp : values) {
      List<Object> value = exp.getValue(paramsMap, s);
      for (Object v : value) {
        if (v == null) {
          r.add(null);
          return r;
        }
        l.add(v);
      }
    }
    r.add(l);
    return r;
  }

  @Override
  public List<Statement> expand() {
    for (int i = 0, valuesSize = values.size(); i < valuesSize; i++) {
      Expression value = values.get(i);
      expanded.set(i, value.expand());
    }
    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  public boolean validForFunctionBody() {
    return super.validForFunctionBody() && values.stream()
      .allMatch(Expression::validForFunctionBody);
  }
}
