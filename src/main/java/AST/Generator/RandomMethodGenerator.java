package AST.Generator;

import AST.Statements.Statement;
import AST.SymbolTable.Method;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Type;
import AST.SymbolTable.Variable;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.RecursiveTask;

public class RandomMethodGenerator {

    public static final double PROB_REUSE_METHOD = 0.75;
    public static final int MAX_METHOD_DEPTH = 5;

    private static int methodDepth = 0;

    public Method generateMethod(List<Type> returnTypes, SymbolTable symbolTable) {
        if (methodDepth > MAX_METHOD_DEPTH) {
            return null;
        }

        RandomTypeGenerator typeGenerator = new RandomTypeGenerator();
        RandomStatementGenerator statementGenerator = new RandomStatementGenerator();

        methodDepth++;
        List<Method> methodWithSameType = symbolTable.getMethodWithTypes(returnTypes);

        double probReuseMethod = GeneratorConfig.getRandom().nextDouble() * Math.pow(GeneratorConfig.DECAY_FACTOR,
            methodDepth - 1);
        if (!methodWithSameType.isEmpty() && probReuseMethod < PROB_REUSE_METHOD) {
            int i = GeneratorConfig.getRandom().nextInt(methodWithSameType.size());
            return methodWithSameType.get(i);
        }

        String methodName = VariableNameGenerator.generateMethodName();
        Method m = new Method(returnTypes, methodName);

        int noOfArgs = GeneratorConfig.getRandom().nextInt(5) + 1;
        List<Type> args = typeGenerator.generateTypes(noOfArgs, symbolTable);
        for (Type t : args) {
            Variable var = new Variable(VariableNameGenerator.generateArgumentName(m), t);
            m.addArgument(var);
        }

        Statement statement = statementGenerator.generateBody(m);
        methodDepth--;
        m.setBody(statement);

        System.out.println(m);

        Method msimple = m.getSimpleMethod();
        symbolTable.addMethod(msimple);

        return msimple;
    }

}