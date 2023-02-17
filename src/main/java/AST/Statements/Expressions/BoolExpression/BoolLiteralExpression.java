package AST.Statements.Expressions.BoolExpression;

import AST.Statements.Expressions.Expression;
import AST.Statements.Statement;
import AST.Statements.Type.ValueGenerator;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Random;

public class BoolLiteralExpression extends Expression<Boolean> {

    private final boolean value;

    public BoolLiteralExpression(Random random, Map<String, Statement> symbolTable) {
        this.value = ValueGenerator.generateBoolValue(random);
    }

    @Override
    public List<Statement> getStatements() {
        return new ArrayList<>();
    }

    @Override
    public Boolean getValue() {
        return value;
    }

    @Override
    public String toString() {
        StringBuilder representation = new StringBuilder();
        representation.append(value);
        return representation.toString();
    }
}
