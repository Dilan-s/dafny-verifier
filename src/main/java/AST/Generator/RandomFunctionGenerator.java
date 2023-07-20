package AST.Generator;

import AST.Expressions.Expression;
import AST.SymbolTable.Function;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.List;
import java.util.stream.Collectors;

public class RandomFunctionGenerator {

    public static final double PROB_REUSE_FUNCTION = 0.75;
    public static final int MAX_FUNCTION_DEPTH = 5;
    public static final int MAX_NO_OF_ARGS = 5;

    private static int functionDepth = 0;

    public Function generateFunction(Type returnType, SymbolTable symbolTable) {
        if (functionDepth > MAX_FUNCTION_DEPTH) {
            return null;
        }

        RandomTypeGenerator typeGenerator = new RandomTypeGenerator();

        List<Function> functionWithSameType = symbolTable.getFunctionWithType(returnType);

        double probReuseFunction = GeneratorConfig.getRandom().nextDouble();

        if (!functionWithSameType.isEmpty() && probReuseFunction < PROB_REUSE_FUNCTION) {
            int i = GeneratorConfig.getRandom().nextInt(functionWithSameType.size());
            return functionWithSameType.get(i);
        }

        int noOfArgs = GeneratorConfig.getRandom().nextInt(MAX_NO_OF_ARGS);
        List<Type> argsT = typeGenerator.generateMethodTypes(noOfArgs, symbolTable);

        return generateFunction(returnType, symbolTable, argsT);
    }

    public Function generateFunction(Type returnType, SymbolTable symbolTable, List<Type> argsT) {

        RandomExpressionGenerator expressionGenerator = new RandomExpressionGenerator();
        RandomMethodGenerator methodGenerator = new RandomMethodGenerator();

        functionDepth++;
        String functionName = VariableNameGenerator.generateFunctionName();

        List<Variable> args = argsT.stream()
            .map(t -> new Variable(VariableNameGenerator.generateArgumentName(functionName), t))
            .collect(Collectors.toList());

        SymbolTable st;
        Expression body;
        do {
            st = new SymbolTable();
            for (Variable arg : args) {
                arg.setConstant();
                for (Variable tableArg : arg.getSymbolTableArgs()) {
                    st.addVariable(tableArg);
                    tableArg.setDeclared();
                }
            }

            methodGenerator.disableMethods();
            body = expressionGenerator.generateExpression(returnType, st);
        } while (body.validForFunction());

        methodGenerator.enableMethods();

        Function f = new Function(functionName, returnType, args, body, st);
        functionDepth--;

        symbolTable.addFunction(f);
        return f;
    }
}