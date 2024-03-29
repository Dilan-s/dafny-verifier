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
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.Variables.Variable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

public class SeqIndexExpression extends BaseExpression {

  private final Statement asStatIndPre;
  private AssignmentStatement asStatSeq;
  private Variable seqVar;
  private final Variable indVar;

  private final SymbolTable symbolTable;
  private final Type type;

  private Optional<AssignmentStatement> asStatInd;

  private final List<List<Statement>> expanded;

  public SeqIndexExpression(SymbolTable symbolTable, Type type, Expression seq, Variable indVar,
    Statement asStatIndPre) {
    super();
    this.symbolTable = symbolTable;
    this.type = type;
    this.indVar = indVar;
    this.asStatIndPre = asStatIndPre;
    setSeqAssignAndIndAssign(seq);

    this.asStatInd = Optional.empty();

    expanded = new ArrayList<>();
    expanded.add(asStatSeq.expand());
    expanded.add(asStatIndPre.expand());
    expanded.add(asStatInd.isPresent() ? asStatInd.get().expand() : new ArrayList<>());
  }

  private void setSeqAssignAndIndAssign(Expression seq) {
    DCollection seqT = seq.getTypes().get(0).asDCollection();
    seqVar = new Variable(VariableNameGenerator.generateVariableValueName(seqT, symbolTable), seqT);
    asStatSeq = new AssignmentStatement(symbolTable, List.of(seqVar), seq);
  }

  public VariableExpression getSequenceVariableExpression() {
    return new VariableExpression(symbolTable, seqVar, seqVar.getType());
  }

  public VariableExpression getIndexVariableExpression() {
    return new VariableExpression(symbolTable, indVar, indVar.getType());
  }

  public void setInd(Map<Variable, Variable> paramsMap, StringBuilder s) {
    DCollection seqT = seqVar.getType().asDCollection();
    VariableExpression seqVarExp = getSequenceVariableExpression();
    VariableExpression indVarExp = getIndexVariableExpression();

    CallBaseMethodExpression exp = new CallBaseMethodExpression(symbolTable,
      symbolTable.getMethod(String.format("safe_index_%s", seqT.getName())),
      List.of(seqVarExp, indVarExp));
    asStatInd = Optional.of(new AssignmentStatement(symbolTable, List.of(indVar), exp));
    List<Statement> expand = asStatInd.get().expand();
    for (Statement stat : expand) {
      stat.execute(paramsMap, s);
    }
    expanded.set(2, asStatInd.get().expand());
  }

  @Override
  public boolean validForFunctionBody() {
    return super.validForFunctionBody() && asStatInd.isEmpty();
  }


  @Override
  public List<Type> getTypes() {
    return List.of(type);
  }

  @Override
  public List<Statement> expand() {
    expanded.set(0, asStatSeq.expand());
    expanded.set(1, asStatIndPre.expand());
    expanded.set(2, asStatInd.isPresent() ? asStatInd.get().expand() : new ArrayList<>());
    return expanded.stream().flatMap(Collection::stream).collect(Collectors.toList());
  }

  @Override
  public String toString() {
    return String.format("%s[%s]", seqVar.getName(), indVar.getName());
  }

  @Override
  protected List<Object> getValue(Map<Variable, Variable> paramsMap, StringBuilder s,
    boolean unused) {
    List<Object> r = new ArrayList<>();

    Object seqVarValue = seqVar.getValue(paramsMap).get(0);
    Object indexValue = indVar.getValue(paramsMap).get(0);

    if (seqVarValue != null && indexValue != null) {
      List<Object> seqVarL = (List<Object>) seqVarValue;
      BigInteger indexValueI = (BigInteger) indexValue;

      if (indexValueI.compareTo(BigInteger.ZERO) >= 0
        && indexValueI.compareTo(BigInteger.valueOf(seqVarL.size())) < 0) {
        r.add(seqVarL.get(indexValueI.intValueExact()));
        return r;
      }
      setInd(paramsMap, s);
      indexValue = indVar.getValue(paramsMap).get(0);
      if (indexValue != null) {
        indexValueI = (BigInteger) indexValue;
        if (indexValueI.compareTo(BigInteger.ZERO) >= 0
          && indexValueI.compareTo(BigInteger.valueOf(seqVarL.size())) < 0) {
          r.add(seqVarL.get(indexValueI.intValueExact()));
          return r;
        }
      }
    }
    r.add(null);
    return r;
  }
}
