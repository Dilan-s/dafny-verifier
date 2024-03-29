package AST.Statements;

import AST.Expressions.Expression;
import AST.Expressions.Function.CallFunctionVariableExpression;
import AST.Expressions.Variable.VariableExpression;
import AST.Generator.VariableNameGenerator;
import AST.Statements.util.ReturnStatus;
import AST.StringUtils;
import AST.SymbolTable.Function.Function;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.PrimitiveTypes.Int.Int;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.Variables.Variable;
import AST.SymbolTable.Types.Variables.VariableArrayIndex;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;

public class ForAllStatement extends BaseStatement {

  private final SymbolTable symbolTable;
  private final int length;
  private final Function func;
  private final Variable variable;
  private Type type;

  private final Variable loopVar;
  private final Statement innerAssignment;
  private final SymbolTable bodySt;

  public ForAllStatement(SymbolTable symbolTable, Type type, int length,
    Function func, Variable variable) {
    super();
    this.symbolTable = symbolTable;
    this.length = length;
    this.func = func;
    this.variable = variable;

    bodySt = new SymbolTable(symbolTable);

    Int loopVarType = new Int();
    this.loopVar = new Variable(
      VariableNameGenerator.generateVariableValueName(loopVarType, bodySt), loopVarType);
    loopVar.setDeclared();

    Variable index = new VariableArrayIndex(variable, type, loopVar);
    index.setDeclared();
    Expression funcCall = new CallFunctionVariableExpression(bodySt, func,
      new VariableExpression(symbolTable, loopVar, type));
    this.innerAssignment = new AssignmentStatement(bodySt, List.of(
      index), funcCall);

  }

  @Override
  protected ReturnStatus execute(Map<Variable, Variable> paramMap, StringBuilder s,
    boolean unused) {
    for (int i = 0; i < length; i++) {
      loopVar.setValue(bodySt, paramMap, BigInteger.valueOf(i));
      innerAssignment.execute(paramMap, s);
    }
    return ReturnStatus.UNKNOWN;
  }

  @Override
  public String toString() {
    List<String> code = new ArrayList<>();
    code.add(
      String.format("forall %s | 0 <= %s < %s.Length {", loopVar.getName(), loopVar.getName(),
        variable.getName()));
    code.add(StringUtils.indent(innerAssignment.toString()));
    code.add("}");

    return StringUtils.intersperse("\n", code);
  }

  @Override
  public List<Statement> expand() {
    return List.of(this);
  }

  @Override
  public List<String> toOutput() {
    return List.of(toString());
  }

  @Override
  public String minimizedTestCase() {
    return toString();
  }
}
