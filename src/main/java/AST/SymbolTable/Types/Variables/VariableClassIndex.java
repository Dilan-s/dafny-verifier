package AST.SymbolTable.Types.Variables;

import AST.Expressions.DClass.DClassValue;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Type;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;

public class VariableClassIndex extends Variable {

  private final String name;
  private final int index;
  private final Variable variable;

  public VariableClassIndex(Variable variable, Type type, String name, int index) {
    super(variable.getName(), type);
    this.variable = variable;
    this.name = name;
    this.index = index;
  }

  @Override
  public List<Object> getValue(Map<Variable, Variable> paramsMap) {
    List<Object> l = new ArrayList<>();
    DClassValue value = (DClassValue) variable.getValue(paramsMap).get(0);
    if (value != null) {
      Object o = value.get(index);
      Object v = type.of(o);
      l.add(v);
    } else {
      l.add(null);
    }
    return l;
  }

  @Override
  public void setValue(SymbolTable symbolTable, Map<Variable, Variable> paramMap, Object value) {
    DClassValue v = (DClassValue) variable.getValue(paramMap).get(0);
    v.set(index, value);
  }

  @Override
  public String getName() {
    return super.getName() + "." + name;
  }

  @Override
  public boolean modified(Variable x) {
    return variable == x;
  }

  @Override
  public List<Variable> getRelatedAssignment() {
    return List.of(variable, this);
  }


  @Override
  public List<Variable> getSymbolTableArgs() {
    List<Variable> symbolTableArgs = super.getSymbolTableArgs();
    symbolTableArgs.forEach(Variable::setConstant);
    return symbolTableArgs;
  }

  @Override
  public int hashCode() {
    return Objects.hash(variable, index, name);
  }

  @Override
  public boolean equals(Object obj) {
    if (!(obj instanceof VariableClassIndex)) {
      return false;
    }
    VariableClassIndex other = (VariableClassIndex) obj;
    return other.variable.equals(variable) && other.index == index && other.name.equals(name);
  }

  @Override
  public boolean isDeclared() {
    return true;
  }
}
