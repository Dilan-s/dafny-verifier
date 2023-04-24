package AST.Statements;

import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public class AssertStatement implements Statement {

    private final SymbolTable symbolTable;
    private final List<Variable> variables;
    private final Set<String> disjuncts;

    public AssertStatement(SymbolTable symbolTable, List<Variable> variables) {
        this.symbolTable = symbolTable;
        this.variables = variables;

        this.disjuncts = new HashSet<>();
    }

    @Override
    public List<Object> execute(Map<Variable, Variable> paramMap, StringBuilder s) {
        List<String> conjuncts = new ArrayList<>();
        for (Variable v : variables) {
            Object val = v.getValue(paramMap).get(0);
            if (val == null) {
                return null;
            }
            String e = v.getType().formatEnsures(v.getName(), val);
            conjuncts.add(e);
        }
        String e = "(" + String.join(" && ", conjuncts) + ")";
        disjuncts.add(e);
        return null;
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
    public String toString() {
        if (disjuncts.size() == 0) {
            return "assert true;";
        }
        return String.format("assert %s;", String.join(" || ", disjuncts));
    }
}