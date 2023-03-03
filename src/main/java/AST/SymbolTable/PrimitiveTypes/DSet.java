package AST.SymbolTable.PrimitiveTypes;

import AST.Generator.RandomTokenGenerator;
import AST.Statements.Expressions.DSetLiteral;
import AST.Statements.Expressions.Expression;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Type;
import java.util.Random;

public class DSet implements Type {

    public static final int MAX_SIZE_OF_SET = 10;
    private Type type;

    public DSet(Type type) {
        this.type = type;
    }

    public DSet() {
        this(null);
    }

    @Override
    public String getName() {
        return String.format("set");
    }

    @Override
    public String getTypeIndicatorString() {
        return String.format(": set<%s>", type.getName());
    }

    @Override
    public Type setInnerType(Type type) {
        return new DSet(type);
    }

    @Override
    public boolean isSameType(Type other) {
        if (!(other instanceof DSet)) {
            return false;
        }

        DSet dsetOther = (DSet) other;

        if (type == null || dsetOther.type == null) {
            return true;
        }

        return dsetOther.type.isSameType(type);
    }

    @Override
    public Expression generateLiteral(Random random, SymbolTable symbolTable) {
        RandomTokenGenerator tokenGenerator = new RandomTokenGenerator(random);

        int noOfElems = random.nextInt(MAX_SIZE_OF_SET) + 1;
        DSetLiteral expression = new DSetLiteral(type);
        for (int i = 0; i < noOfElems; i++) {
            expression.addValue(tokenGenerator.generateExpression(type, symbolTable));
        }
        return expression;
    }

    @Override
    public boolean operatorExists() {
        return true;
    }

    @Override
    public boolean isPrintable() {
        return false;
    }

    @Override
    public boolean isCollection() {
        return true;
    }
}