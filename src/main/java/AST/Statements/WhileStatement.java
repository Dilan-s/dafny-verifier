package AST.Statements;

import AST.Expressions.Expression;
import AST.Generator.GeneratorConfig;
import AST.Statements.util.ReturnStatus;
import AST.StringUtils;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class WhileStatement extends BaseStatement {

  private final SymbolTable symbolTable;
  private final Variable loopVar;
  private final Variable finalVar;
  private final Statement initAssign;
  private final Statement finalAssign;
  private final Expression test;
  private final Statement body;
  private final Map<String, Set<String>> loopInvariants;

  private final List<List<Statement>> expanded;

  public WhileStatement(SymbolTable symbolTable, Variable loopVar, Variable finalVar,
    Statement initAssign, Statement finalAssign, Expression test, Statement body) {
    this.symbolTable = symbolTable;
    this.loopVar = loopVar;
    this.finalVar = finalVar;
    this.initAssign = initAssign;
    this.finalAssign = finalAssign;
    this.test = test;
    this.body = body;
    this.loopInvariants = new HashMap<>();

    this.expanded = new ArrayList<>();
    expanded.add(initAssign.expand());
    expanded.add(finalAssign.expand());
    expanded.add(test.expand());
    expanded.add(List.of(this));
  }

  @Override
  public Set<Variable> getModifies() {
    return body.getModifies();
  }

  @Override
  protected ReturnStatus execute(Map<Variable, Variable> paramMap, StringBuilder s,
    boolean unused) {
    while (true) {
      Object testValue = test.getValue(paramMap, s).get(0);

      Boolean testValueB = (Boolean) testValue;
      Set<Variable> modSet = body.getModifies();
      addInvariantForModSet(modSet, paramMap);
      if (testValueB) {
        ReturnStatus execute = body.execute(paramMap, s);
        if (execute == ReturnStatus.RETURN) {
          return execute;
        } else if (execute == ReturnStatus.BREAK) {
          if (execute.getDepth() > 0) {
            return ReturnStatus.breakWithDepth(execute.getDepth() - 1);
          }
          return ReturnStatus.UNKNOWN;
        }
      } else {
        return ReturnStatus.UNKNOWN;
      }
    }
  }

  private void addInvariantForModSet(Set<Variable> modSet, Map<Variable, Variable> paramMap) {
    Set<Variable> vs = modSet.stream()
      .filter(v -> symbolTable.getAllVariables(v.getType()).contains(v))
      .filter(v -> v != loopVar)
      .collect(Collectors.toSet());

    if (!vs.isEmpty()) {

      Object value = loopVar.getValue(paramMap).get(0);
      String key = loopVar.getType().formatEnsures(loopVar.getName(), value);

      if (!loopInvariants.containsKey(key)) {
        loopInvariants.put(key, new HashSet<>());
      }
      Set<String> invs = loopInvariants.get(key);

      List<String> rhs = new ArrayList<>();
      for (Variable v : vs) {
        Object obj = v.getValue(paramMap).get(0);
        rhs.add(String.format("(%s)", v.getType().formatEnsures(v.getName(), obj)));
      }
      String rhsV = "(" + String.join(" && ", rhs) + ")";
      invs.add(rhsV);

    }
  }

  @Override
  public List<Statement> expand() {
    expanded.set(0, initAssign.expand());
    expanded.set(1, finalAssign.expand());
    expanded.set(2, test.expand());
    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  public List<String> toOutput() {
    Set<String> res = new HashSet<>();

    List<String> testOptions = test.toOutput();
    for (String testOption : testOptions) {
      String curr = String.format("while %s \n", testOption);

      if (!loopInvariants.isEmpty()) {
        curr = curr + StringUtils.indent(
          String.format("decreases %s - %s", finalVar.getName(), loopVar.getName())) + "\n";
        curr = curr + StringUtils.indent(
          String.format("invariant (%s <= %s)", loopVar.getName(), finalVar.getName()));

        List<String> loopInvariants = this.loopInvariants.entrySet().stream()
          .distinct()
          .map(x -> String.format("((%s) ==> (%s))", x.getKey(), String.join(" || ", x.getValue())))
          .collect(Collectors.toList());

        curr = curr + " && (" + String.join(" && ", loopInvariants) + ")";
        curr = curr + "\n{\n";
      } else {
        curr = curr + "{\n";

      }

      res.add(curr);
    }

    List<String> temp = new ArrayList<>();
    List<String> bodyOptions = body.toOutput();
    for (String f : res) {
      for (String bodyOption : bodyOptions) {
        String curr = f + StringUtils.indent(bodyOption);
        temp.add(curr);
      }
    }
    if (bodyOptions.isEmpty()) {
      temp.addAll(res);
    }

    res = new HashSet<>(temp);
    temp = new ArrayList<>();
    for (String f : res) {
      String curr = f + "\n}";
      temp.add(curr);
    }

    res = new HashSet<>(temp);

    List<String> r = new ArrayList<>(res);
    Collections.shuffle(r, GeneratorConfig.getRandom());
    return r.subList(0, Math.min(5, r.size()));
  }

  @Override
  public String minimizedTestCase() {
    if (body.getNoOfUses() > 0) {
      String res = String.format("while %s \n", test);

      if (!loopInvariants.isEmpty()) {
        res = res + StringUtils.indent(
          String.format("decreases %s - %s", finalVar.getName(), loopVar.getName())) + "\n";
        res = res + StringUtils.indent(
          String.format("invariant (%s <= %s)", loopVar.getName(), finalVar.getName()));

        List<String> loopInvariants = this.loopInvariants.entrySet().stream()
          .distinct()
          .map(x -> String.format("((%s) ==> (%s))", x.getKey(),
            String.join(" || ", x.getValue())))
          .collect(Collectors.toList());

        res = res + " && (" + String.join(" && ", loopInvariants) + ")";
        res = res + "\n{\n";
      } else {
        res = res + "{\n";

      }

      res = res + StringUtils.indent(body.minimizedTestCase());
      res = res + "\n}";

      return res;
    }
    return "";
  }

  @Override
  public Map<String, String> invalidValidationTests() {
    if (body.getNoOfUses() > 0) {
      return body.invalidValidationTests();
    }
    return new HashMap<>();
  }

  @Override
  public String toString() {
    String res = String.format("while %s \n", test);

    if (!loopInvariants.isEmpty()) {
      res = res + StringUtils.indent(
        String.format("decreases %s - %s", finalVar.getName(), loopVar.getName())) + "\n";
      res = res + StringUtils.indent(
        String.format("invariant (%s <= %s)", loopVar.getName(), finalVar.getName()));

      List<String> loopInvariants = this.loopInvariants.entrySet().stream()
        .distinct()
        .map(x -> String.format("((%s) ==> (%s))", x.getKey(),
          String.join(" || ", x.getValue())))
        .collect(Collectors.toList());

      res = res + " && (" + String.join(" && ", loopInvariants) + ")";
      res = res + "\n{\n";
    } else {
      res = res + "{\n";

    }
    res = res + StringUtils.indent(body.toString());
    res = res + "\n}";

    return res;
  }

  @Override
  public boolean validForFunctionBody() {
    return false;
  }
}
