package AST.Expressions.DSeq;

import AST.Expressions.BaseExpression;
import AST.Expressions.Expression;
import AST.Expressions.Method.CallBaseMethodExpression;
import AST.Expressions.Variable.VariableExpression;
import AST.Generator.VariableNameGenerator;
import AST.Statements.AssignmentStatement;
import AST.Statements.Statement;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.DCollectionTypes.DCollection;
import AST.SymbolTable.Types.PrimitiveTypes.Int.Int;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.Variables.Variable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class SeqSubsequenceExpression extends BaseExpression {

  private final Expression i;
  private final Expression j;

  private Expression min;
  private Expression max;

  private final SymbolTable symbolTable;

  private AssignmentStatement statSeq;
  private Variable seqVar;

  private Optional<AssignmentStatement> statLoHi;
  private Optional<Variable> loVar;
  private Optional<Variable> hiVar;
  private Optional<CallBaseMethodExpression> callExp;

  private List<List<Statement>> expanded;

  public SeqSubsequenceExpression(SymbolTable symbolTable, Expression seq, Expression i,
    Expression j) {
    super();
    this.symbolTable = symbolTable;
    this.i = i;
    this.j = j;
    this.min = null;
    this.max = null;
    setSeqAssign(seq);
    this.statLoHi = Optional.empty();
    this.loVar = Optional.empty();
    this.hiVar = Optional.empty();
    this.callExp = Optional.empty();

    expanded = new ArrayList<>();
    expanded.add(statSeq.expand());
    expanded.add(i.expand());
    expanded.add(j.expand());
  }

  private void setSeqAssign(Expression seq) {
    DCollection seqType = seq.getTypes().get(0).asDCollection();
    seqVar = new Variable(VariableNameGenerator.generateVariableValueName(seqType, symbolTable),
      seqType);

    statSeq = new AssignmentStatement(symbolTable, List.of(seqVar), seq);
  }

  public VariableExpression getSequenceVariableExpression() {
    return new VariableExpression(symbolTable, seqVar, seqVar.getType());
  }

  private void setIndIandJ(Map<Variable, Variable> paramsMap, StringBuilder s) {
    VariableExpression seqVarExp = getSequenceVariableExpression();

    Int loT = new Int();
    Int hiT = new Int();

    Variable loV = new Variable(VariableNameGenerator.generateVariableValueName(loT, symbolTable),
      loT);
    Variable hiV = new Variable(VariableNameGenerator.generateVariableValueName(hiT, symbolTable),
      hiT);
    CallBaseMethodExpression exp = new CallBaseMethodExpression(symbolTable,
      symbolTable.getMethod("safe_subsequence"), List.of(seqVarExp, i, j));
    this.loVar = Optional.of(loV);
    this.hiVar = Optional.of(hiV);
    this.callExp = Optional.of(exp);
    this.statLoHi = Optional.of(new AssignmentStatement(symbolTable, List.of(loV, hiV), exp));

    for (Statement stat : statLoHi.get().expand()) {
      stat.execute(paramsMap, s);
    }

    expanded = new ArrayList<>();
    expanded.add(statSeq.expand());
    expanded.add(statLoHi.get().expand());
  }

  @Override
  public boolean validForFunctionBody() {
    return false;
  }

  @Override
  public List<Type> getTypes() {
    return List.of(seqVar.getType());
  }

  @Override
  public List<Statement> expand() {
    expanded.set(0, statSeq.expand());
    if (statLoHi.isPresent()) {
      expanded.set(1, statLoHi.get().expand());
    } else {
      expanded.set(1, i.expand());
      expanded.set(2, j.expand());
    }

    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  public String toString() {
    if (loVar.isPresent() && hiVar.isPresent() && callExp.isPresent() && statLoHi.isPresent()) {
      return String.format("%s[%s..%s]", seqVar.getName(), loVar.get().getName(),
        hiVar.get().getName());
    } else if (this.min != null && this.max != null) {
      return String.format("%s[%s..%s]", seqVar.getName(), min, max);
    }
    return String.format("%s[%s..%s]", seqVar.getName(), i, j);
  }

  @Override
  public String minimizedTestCase() {
    if (loVar.isPresent() && hiVar.isPresent() && callExp.isPresent() && statLoHi.isPresent()) {
      return String.format("%s[%s..%s]", seqVar.getName(), loVar.get().getName(),
        hiVar.get().getName());
    } else if (this.min != null && this.max != null) {
      return String.format("%s[%s..%s]", seqVar.getName(), min.minimizedTestCase(),
        max.minimizedTestCase());
    }
    return String.format("%s[%s..%s]", seqVar.getName(), i.minimizedTestCase(),
      j.minimizedTestCase());
  }

  @Override
  protected List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s,
    boolean unused) {
    List<Object> r = new ArrayList<>();

    Object seqVarValue = seqVar.getValue(paramsMap).get(0);

    if (seqVarValue != null) {
      List<Object> seqVarL = (List<Object>) seqVarValue;

      if (loVar.isPresent() && hiVar.isPresent()) {
        Object loVarValue = loVar.get().getValue(paramsMap).get(0);
        Object hiVarValue = hiVar.get().getValue(paramsMap).get(0);

        if (loVarValue != null && hiVarValue != null) {
          BigInteger loVarI = (BigInteger) loVarValue;
          BigInteger hiVarI = (BigInteger) hiVarValue;

          r.add(seqVarL.subList(loVarI.intValueExact(), hiVarI.intValueExact()));
          return r;
        }
      }

      if (min != null && max != null) {
        Object minValue = min.getValue(paramsMap).get(0);
        Object maxValue = max.getValue(paramsMap).get(0);

        if (minValue != null && maxValue != null) {
          BigInteger loVarI = (BigInteger) minValue;
          BigInteger hiVarI = (BigInteger) maxValue;

          r.add(seqVarL.subList(loVarI.intValueExact(), hiVarI.intValueExact()));
          return r;

        }
        r.add(null);
        return r;
      }

      Object iValue = i.getValue(paramsMap).get(0);
      Object jValue = j.getValue(paramsMap).get(0);

      if (iValue != null && jValue != null) {
        BigInteger iI = (BigInteger) iValue;
        BigInteger jI = (BigInteger) jValue;

        if (iI.compareTo(BigInteger.ZERO) >= 0
          && iI.compareTo(BigInteger.valueOf(seqVarL.size())) < 0 &&
          jI.compareTo(BigInteger.ZERO) >= 0
          && jI.compareTo(BigInteger.valueOf(seqVarL.size())) < 0) {
          this.min = iI.compareTo(jI) < 0 ? i : j;
          this.max = iI.compareTo(jI) <= 0 ? j : i;

          BigInteger minI = iI.compareTo(jI) < 0 ? iI : jI;
          BigInteger maxI = iI.compareTo(jI) <= 0 ? jI : iI;

          r.add(seqVarL.subList(minI.intValueExact(), maxI.intValueExact()));
          return r;
        }
        setIndIandJ(paramsMap, s);

        Object loVarValue = loVar.get().getValue(paramsMap).get(0);
        Object hiVarValue = hiVar.get().getValue(paramsMap).get(0);

        if (loVarValue != null && hiVarValue != null) {
          BigInteger loVarI = (BigInteger) loVarValue;
          BigInteger hiVarI = (BigInteger) hiVarValue;

          r.add(seqVarL.subList(loVarI.intValueExact(), hiVarI.intValueExact()));
          return r;
        }
      }
    }
    r.add(null);
    return r;
  }
}
