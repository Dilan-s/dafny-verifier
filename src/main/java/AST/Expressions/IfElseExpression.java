package AST.Expressions;

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

public class IfElseExpression extends BaseExpression {

  private final Expression test;
  private final Expression ifExp;
  private final Expression elseExp;
  private final Type type;
  private final SymbolTable symbolTable;

  private final List<List<Statement>> expanded;

  public IfElseExpression(SymbolTable symbolTable, Type type, Expression test, Expression ifExp,
    Expression elseExp) {
    super();
    this.symbolTable = symbolTable;
    this.type = type;
    this.test = test;
    this.ifExp = ifExp;
    this.elseExp = elseExp;

    this.expanded = new ArrayList<>();
    expanded.add(test.expand());
    expanded.add(ifExp.expand());
    expanded.add(elseExp.expand());
  }

  @Override
  public List<Type> getTypes() {
    return List.of(type);
  }

  @Override
  public String minimizedTestCase() {
    if (ifExp.getNoOfUses() > 0 && elseExp.getNoOfUses() > 0) {
      return String.format("(if (%s) then (%s) else (%s))", test.minimizedTestCase(),
        ifExp.minimizedTestCase(), elseExp.minimizedTestCase());
    }
    if (elseExp.getNoOfUses() > 0) {
      return String.format("(%s)", elseExp.minimizedTestCase());
    }
    if (ifExp.getNoOfUses() > 0) {
      return String.format("(%s)", ifExp.minimizedTestCase());
    }

    return toString();
  }

  @Override
  public String toString() {
    return String.format("(if (%s) then (%s) else (%s))", test, ifExp, elseExp);
  }

  @Override
  public List<String> toOutput() {
    Set<String> res = new HashSet<>();
    List<String> temp = new ArrayList<>();

    res.add("(if (");

    List<String> testOptions = test.toOutput();
    temp = new ArrayList<>();
    for (String f : res) {
      for (String testOption : testOptions) {
        String curr = f + testOption;
        temp.add(curr);
      }
    }
    if (testOptions.isEmpty()) {
      temp.addAll(res);
    }
    res = new HashSet<>(temp);

    temp = new ArrayList<>();
    for (String f : res) {
      temp.add(f + ") then (");
    }
    res = new HashSet<>(temp);

    List<String> ifOptions = ifExp.toOutput();
    temp = new ArrayList<>();
    for (String f : res) {
      for (String ifOption : ifOptions) {
        String curr = f + ifOption;
        temp.add(curr);
      }
    }
    if (ifOptions.isEmpty()) {
      temp.addAll(res);
    }
    res = new HashSet<>(temp);

    temp = new ArrayList<>();
    for (String f : res) {
      temp.add(f + ") else (");
    }
    res = new HashSet<>(temp);

    List<String> elseOptions = elseExp.toOutput();
    temp = new ArrayList<>();
    for (String f : res) {
      for (String testOption : elseOptions) {
        String curr = f + testOption;
        temp.add(curr);
      }
    }
    if (elseOptions.isEmpty()) {
      temp.addAll(res);
    }
    res = new HashSet<>(temp);

    temp = new ArrayList<>();
    for (String f : res) {
      temp.add(f + "))");
    }
    res = new HashSet<>(temp);

    List<String> r = new ArrayList<>(res);
    Collections.shuffle(r, GeneratorConfig.getRandom());
    return r.subList(0, Math.min(5, res.size()));
  }

  @Override
  public boolean isValidReturn() {
    return ifExp.isValidReturn() && elseExp.isValidReturn();
  }

  @Override
  protected List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s,
    boolean unused) {
    List<Object> r = new ArrayList<>();

    Object testValue = test.getValue(paramsMap, s).get(0);

    if (testValue != null) {
      Boolean testB = (Boolean) testValue;
      if (testB) {
        return ifExp.getValue(paramsMap, s);
      } else {
        return elseExp.getValue(paramsMap, s);
      }
    }
    r.add(null);
    return r;
  }

  @Override
  public List<Statement> expand() {
    expanded.set(0, test.expand());
    expanded.set(1, ifExp.expand());
    expanded.set(2, elseExp.expand());
    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  public boolean validForFunctionBody() {
    return super.validForFunctionBody()
      && test.validForFunctionBody()
      && ifExp.validForFunctionBody()
      && elseExp.validForFunctionBody();
  }
}
