package AST.Statements;

import AST.Expressions.Expression;
import AST.Generator.GeneratorConfig;
import AST.Statements.util.MatchStatementCase;
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

public class MatchStatement extends BaseStatement {

  private final SymbolTable symbolTable;
  private final Expression test;
  private final List<MatchStatementCase> cases;
  private final List<MatchStatementCase> distinctCases;
  private final MatchStatementCase defaultCase;

  private final List<List<Statement>> expanded;

  public MatchStatement(SymbolTable symbolTable, Expression test, List<MatchStatementCase> cases,
    MatchStatementCase defaultCase) {
    super();
    this.symbolTable = symbolTable;
    this.test = test;
    this.cases = cases;
    this.defaultCase = defaultCase;
    this.distinctCases = new ArrayList<>(cases);

    this.expanded = new ArrayList<>();

    this.expanded.add(test.expand());
    cases.forEach(c -> expanded.add(c.expand()));
    expanded.add(defaultCase.expand());
    expanded.add(List.of(this));
  }

  @Override
  public boolean isReturn() {
    return distinctCases.stream().allMatch(Statement::isReturn) && defaultCase.isReturn();
  }

  @Override
  protected ReturnStatus execute(Map<Variable, Variable> paramMap, StringBuilder s,
    boolean unused) {
    Object testValue = test.getValue(paramMap).get(0);
    if (testValue == null) {
      return null;
    }

    List<MatchStatementCase> cases = new ArrayList<>(this.distinctCases);
    Set<Object> testValues = new HashSet<>();

    for (int i = 0; i < cases.size(); i++) {
      MatchStatementCase matchStatementCase = cases.get(i);

      Object castTestValue = matchStatementCase.getTest().getValue(paramMap).get(0);
      if (castTestValue == null) {
        return null;
      }

      if (testValues.contains(castTestValue)) {
        distinctCases.remove(matchStatementCase);
        continue;
      }
      testValues.add(castTestValue);

      if (castTestValue.equals(testValue)) {
        ReturnStatus execute = matchStatementCase.execute(paramMap, s);
        for (int j = i + 1; j < cases.size(); j++) {
          matchStatementCase = cases.get(j);

          castTestValue = matchStatementCase.getTest().getValue(paramMap).get(0);
          if (castTestValue == null) {
            return null;
          }

          if (testValues.contains(castTestValue)) {
            distinctCases.remove(matchStatementCase);
          } else {
            testValues.add(castTestValue);
          }
        }
        return execute;
      }
    }
    return defaultCase.execute(paramMap, s);
  }

  @Override
  public Set<Variable> getModifies() {
    Set<Variable> res = distinctCases.stream()
      .map(MatchStatementCase::getModifies)
      .flatMap(Collection::stream)
      .collect(Collectors.toSet());
    res.addAll(defaultCase.getModifies());
    return res;
  }

  @Override
  public List<Statement> expand() {
    int i = 0;
    expanded.set(i, test.expand());
    i++;

    for (int j = 0; j < cases.size(); j++) {
      MatchStatementCase c = cases.get(j);
      expanded.set(i, c.expand());
      i++;
    }
    expanded.set(i, defaultCase.expand());
    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  public List<String> toOutput() {
    Set<String> res = new HashSet<>();
    List<String> temp = new ArrayList<>();

    List<String> testOutputs = test.toOutput();
    for (String testOutput : testOutputs) {
      res.add(String.format("match %s {\n", testOutput));
    }

    if (getNoOfUses() > 0) {
      for (MatchStatementCase matchStatementCase : distinctCases) {
        List<String> caseOptions = matchStatementCase.toOutput();
        temp = new ArrayList<>();
        for (String f : res) {
          for (String caseOption : caseOptions) {
            String curr = StringUtils.indent(caseOption);
            curr = f + curr + "\n";
            temp.add(curr);
          }
        }
        if (caseOptions.isEmpty()) {
          temp.addAll(res);
        }

        res = new HashSet<>(temp);

        List<String> r = new ArrayList<>(res);
        Collections.shuffle(r, GeneratorConfig.getRandom());
        res = new HashSet<>(r.subList(0, Math.min(5, r.size())));
      }
    }

    temp = new ArrayList<>();
    List<String> defaultOptions = defaultCase.toOutput();
    for (String f : res) {
      for (String defaultOption : defaultOptions) {
        String curr = StringUtils.indent(defaultOption);
        curr = f + curr + "\n";
        temp.add(curr);
      }
    }
    if (defaultOptions.isEmpty()) {
      temp.addAll(res);
    }

    res = new HashSet<>(temp);

    temp = new ArrayList<>();
    for (String f : res) {
      temp.add(f + "}\n");
    }

    res = new HashSet<>(temp);

    List<String> r = new ArrayList<>(res);
    Collections.shuffle(r, GeneratorConfig.getRandom());
    return r.subList(0, Math.min(5, r.size()));
  }

  @Override
  public String minimizedTestCase() {
    List<MatchStatementCase> usedCases = new ArrayList<>();
    distinctCases.stream().filter(c -> c.getNoOfUses() > 0).forEach(usedCases::add);
    if (defaultCase.getNoOfUses() > 0) {
      usedCases.add(defaultCase);
    }

    if (usedCases.size() == 1) {
      Statement body = usedCases.get(0).getBody();
      String res = body.minimizedTestCase();
      return res;
    } else if (usedCases.size() > 1) {

      String res = String.format("match %s {\n", test.minimizedTestCase());
      for (MatchStatementCase c : usedCases) {
        res = res + StringUtils.indent(c.minimizedTestCase());
      }
      res = res + "\n}\n";
      return res;
    }

    return "";
  }

  @Override
  public Map<String, String> invalidValidationTests() {
    List<MatchStatementCase> usedCases = new ArrayList<>();
    distinctCases.stream().filter(c -> c.getNoOfUses() > 0).forEach(usedCases::add);
    if (defaultCase.getNoOfUses() > 0) {
      usedCases.add(defaultCase);
    }

    if (usedCases.size() == 1) {
      Statement body = usedCases.get(0).getBody();
      return body.invalidValidationTests();
    } else if (usedCases.size() > 1) {
      Map<String, String> res = new HashMap<>();
      for (MatchStatementCase c : usedCases) {
        Map<String, String> m = c.invalidValidationTests();
        res.putAll(m);

      }
      return res;
    }

    return new HashMap<>();
  }

  @Override
  public String toString() {
    String res = String.format("match %s {\n", test.toString());
    if (getNoOfUses() > 0) {
      for (MatchStatementCase c : distinctCases) {
        res = res + StringUtils.indent(c.toString());
      }
    }
    res = res + StringUtils.indent(defaultCase.toString());
    res = res + "\n}\n";
    return res;
  }

  @Override
  public boolean validForFunctionBody() {
    return false;
  }
}
