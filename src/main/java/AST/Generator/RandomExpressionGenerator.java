package AST.Generator;

import AST.Expressions.DMap.DMapSelection;
import AST.Expressions.DMap.DMapUpdateExpression;
import AST.Expressions.DSeq.SeqFromArrayExpression;
import AST.Expressions.DSeq.SeqIndexExpression;
import AST.Expressions.DSeq.SeqSubsequenceExpression;
import AST.Expressions.DSeq.SeqUpdateExpression;
import AST.Expressions.Expression;
import AST.Expressions.Function.CallFunctionExpression;
import AST.Expressions.Function.CallVariableExpression;
import AST.Expressions.IfElseExpression;
import AST.Expressions.IntLiteral;
import AST.Expressions.Match.MatchExpression;
import AST.Expressions.Match.MatchExpressionCase;
import AST.Expressions.Method.CallMethodExpression;
import AST.Expressions.Operator.BinaryOperator;
import AST.Expressions.Operator.Operator;
import AST.Expressions.Operator.OperatorExpression;
import AST.Expressions.Operator.UnaryOperator;
import AST.Expressions.Variable.VariableExpression;
import AST.Statements.AssignmentStatement;
import AST.Statements.Statement;
import AST.SymbolTable.Function.Function;
import AST.SymbolTable.Method.Method;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.DCollectionTypes.DArray;
import AST.SymbolTable.Types.DCollectionTypes.Seq;
import AST.SymbolTable.Types.DMap.DMap;
import AST.SymbolTable.Types.PrimitiveTypes.Bool;
import AST.SymbolTable.Types.PrimitiveTypes.Int.Int;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.UserDefinedTypes.ArrowType;
import AST.SymbolTable.Types.Variables.Variable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public class RandomExpressionGenerator {

  public static final double PROB_HI_AND_LO_SUBSEQUENCE = 0.7;
  public static final int MAX_EXPRESSION_DEPTH = 3;
  private static final int MAX_MATCH_CASES_VALUES = 2;
  public static double PROB_LITERAL_EXPRESSION = 60.0;
  public static double PROB_OPERATOR_EXPRESSION = 30.0;
  public static double PROB_VARIABLE_EXPRESSION = 60.0;
  public static double PROB_SEQ_INDEX_EXPRESSION = 8.0;
  public static double PROB_DMAP_SELECTION_EXPRESSION = 8.0;
  public static double PROB_SEQ_SUBSEQUENCE_EXPRESSION = 8.0;
  public static double PROB_SEQ_UPDATE_EXPRESSION = 8.0;
  public static double PROB_SEQ_FROM_ARRAY_EXPRESSION = 8.0;
  public static double PROB_DMAP_UPDATE_EXPRESSION = 8.0;
  public static double PROB_IF_ELSE_EXPRESSION = 8.0;
  public static double PROB_CALL_METHOD_EXPRESSION = 20.0;
  public static double PROB_CALL_FUNCTION_EXPRESSION = 20.0;
  public static double PROB_MATCH_EXPRESSION = 5.0;
  public static double PROB_CALL_VARIABLE_EXPRESSION = 10.0;
  private static int expressionDepth = 0;

  public Expression generateExpression(Type type, SymbolTable symbolTable) {
    Expression ret = null;
    expressionDepth++;
    while (ret == null) {
      double ratioSum = PROB_LITERAL_EXPRESSION + PROB_OPERATOR_EXPRESSION +
        PROB_VARIABLE_EXPRESSION + PROB_SEQ_INDEX_EXPRESSION + PROB_DMAP_SELECTION_EXPRESSION +
        PROB_SEQ_SUBSEQUENCE_EXPRESSION + PROB_SEQ_UPDATE_EXPRESSION
        + PROB_SEQ_FROM_ARRAY_EXPRESSION +
        PROB_DMAP_UPDATE_EXPRESSION + PROB_IF_ELSE_EXPRESSION + PROB_CALL_METHOD_EXPRESSION
        + PROB_CALL_FUNCTION_EXPRESSION + PROB_MATCH_EXPRESSION + PROB_CALL_VARIABLE_EXPRESSION;

      double probTypeOfExpression = GeneratorConfig.getRandom().nextDouble() * ratioSum;
      if (expressionDepth > MAX_EXPRESSION_DEPTH
        || (probTypeOfExpression -= PROB_LITERAL_EXPRESSION) < 0) {
        //literal
        ret = generateLiteral(type, symbolTable);

      } else if ((probTypeOfExpression -= PROB_VARIABLE_EXPRESSION) < 0) {
        //variable
        PROB_VARIABLE_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
        VariableExpression expression = generateVariableExpression(type, symbolTable);
        if (expression != null) {
          ret = expression;
        }
      } else if ((probTypeOfExpression -= PROB_OPERATOR_EXPRESSION) < 0 && type.operatorExists()) {
        //Operator
        PROB_OPERATOR_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
        OperatorExpression expression = generateOperatorExpression(type, symbolTable);
        if (expression != null) {
          ret = expression;
        }
      } else if ((probTypeOfExpression -= PROB_SEQ_INDEX_EXPRESSION) < 0) {
        PROB_SEQ_INDEX_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
        ret = generateSeqIndexExpression(type, symbolTable);
      } else if ((probTypeOfExpression -= PROB_DMAP_SELECTION_EXPRESSION) < 0) {
        PROB_DMAP_SELECTION_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
        ret = generateDMapSelectionExpression(type, symbolTable);
      } else if ((probTypeOfExpression -= PROB_SEQ_SUBSEQUENCE_EXPRESSION) < 0) {
        if (type.equals(new Seq())) {
          PROB_SEQ_SUBSEQUENCE_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
          ret = generateSeqSubsequenceExpression(type, symbolTable);
        }
      } else if ((probTypeOfExpression -= PROB_SEQ_UPDATE_EXPRESSION) < 0) {
        if (type.equals(new Seq())) {
          PROB_SEQ_UPDATE_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
          ret = generateSeqUpdateExpression(type, symbolTable);
        }
      } else if ((probTypeOfExpression -= PROB_SEQ_FROM_ARRAY_EXPRESSION) < 0) {
        if (type.equals(new Seq())) {
          PROB_SEQ_FROM_ARRAY_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
          ret = generateSeqFromArray(type, symbolTable);
        }
      } else if ((probTypeOfExpression -= PROB_DMAP_UPDATE_EXPRESSION) < 0) {
        if (type.equals(new DMap())) {
          PROB_DMAP_UPDATE_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
          ret = generateDMapUpdateExpression(type, symbolTable);
        }
      } else if ((probTypeOfExpression -= PROB_IF_ELSE_EXPRESSION) < 0) {
        //ifElse
        PROB_IF_ELSE_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
        ret = generateIfElseExpression(type, symbolTable);

      } else if ((probTypeOfExpression -= PROB_CALL_METHOD_EXPRESSION) < 0) {
        //call
        if (type.validMethodType()) {
          PROB_CALL_METHOD_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
          ret = generateCallMethodExpression(symbolTable, List.of(type));
        }
      } else if ((probTypeOfExpression -= PROB_CALL_FUNCTION_EXPRESSION) < 0) {
        //call
        if (type.validForFunctionBody()) {
          PROB_CALL_FUNCTION_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
          ret = generateCallFunctionExpression(type, symbolTable);
        }
      } else if ((probTypeOfExpression -= PROB_CALL_VARIABLE_EXPRESSION) < 0) {
        if (type.validForFunctionBody()) {
          PROB_CALL_VARIABLE_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
          ret = generateVariableCallExpression(type, symbolTable);
        }
      } else if ((probTypeOfExpression -= PROB_MATCH_EXPRESSION) < 0) {
        //match
        PROB_MATCH_EXPRESSION *= GeneratorConfig.OPTION_DECAY_FACTOR;
        ret = generateMatchExpression(type, symbolTable);
      }
    }
    expressionDepth--;
    return ret;
  }

  private Expression generateMatchExpression(Type type, SymbolTable symbolTable) {
    int noOfCases = GeneratorConfig.getRandom().nextInt(MAX_MATCH_CASES_VALUES) + 1;

    RandomTypeGenerator typeGenerator = new RandomTypeGenerator();
    Type t = typeGenerator.generateMatchType(symbolTable).concrete(symbolTable);

    expressionDepth += MAX_EXPRESSION_DEPTH;
    Expression test = generateExpression(t, symbolTable);
    expressionDepth -= MAX_EXPRESSION_DEPTH;

    List<MatchExpressionCase> cases = new ArrayList<>();
    for (int i = 0; i < noOfCases; i++) {
      SymbolTable caseSymbolTable = new SymbolTable(symbolTable);

      Expression testCase = generateLiteral(t, caseSymbolTable);
      Expression value = generateExpression(type, caseSymbolTable);

      MatchExpressionCase c = new MatchExpressionCase(caseSymbolTable, type, testCase, value);
      cases.add(c);
    }

    SymbolTable defCaseSymbolTable = new SymbolTable(symbolTable);
    Expression defCaseValue = generateExpression(type, defCaseSymbolTable);

    MatchExpressionCase defCase = new MatchExpressionCase(defCaseSymbolTable, type, defCaseValue);
    MatchExpression matchExpression = new MatchExpression(symbolTable, type, test, cases, defCase);
    return matchExpression;
  }

  private Expression generateVariableCallExpression(Type type, SymbolTable symbolTable) {
    ArrowType arrowType = new ArrowType(type).concrete(symbolTable).asArrowType();

    Expression arrowTypeExpression = generateExpression(arrowType, symbolTable);

    List<Expression> args = arrowType.getFromTypes().stream()
      .map(t -> generateExpression(t, symbolTable))
      .collect(Collectors.toList());

    Variable funcVariable = new Variable(
      VariableNameGenerator.generateVariableValueName(arrowType, symbolTable), arrowType);
    Statement funcVariableAssign = new AssignmentStatement(symbolTable, List.of(funcVariable),
      arrowTypeExpression);

    return new CallVariableExpression(symbolTable, type, funcVariable, funcVariableAssign, args);
  }

  private Expression generateDMapUpdateExpression(Type type, SymbolTable symbolTable) {
    DMap mapT = type.concrete(symbolTable).asDMap();

    Expression map = generateExpression(type, symbolTable);
    Expression key = generateExpression(mapT.getKeyType(), symbolTable);
    Expression value = generateExpression(mapT.getValueType(), symbolTable);

    DMapUpdateExpression mapUpdateExpression = new DMapUpdateExpression(symbolTable, type, map,
      key, value);
    return mapUpdateExpression;
  }

  private Expression generateSeqFromArray(Type type, SymbolTable symbolTable) {
    Seq seq = type.asSeq();
    DArray array = new DArray(seq.getInnerType()).concrete(symbolTable).asDArray();

    Expression arraySeq = generateExpression(array, symbolTable);
    Variable funcVariable = new Variable(
      VariableNameGenerator.generateVariableValueName(array, symbolTable), array);
    Statement funcVariableAssign = new AssignmentStatement(symbolTable, List.of(funcVariable),
      arraySeq);

    SeqFromArrayExpression expression = new SeqFromArrayExpression(symbolTable, type, funcVariable,
      funcVariableAssign);
    return expression;

  }

  private Expression generateSeqUpdateExpression(Type type, SymbolTable symbolTable) {
    Seq seqT = type.concrete(symbolTable).asSeq();
    Expression seq = generateExpression(seqT, symbolTable);

    Int indT = new Int();
    Expression ind = generateExpression(indT, symbolTable);

    Type expT = seqT.getInnerType().concrete(symbolTable);
    Expression exp = generateExpression(expT, symbolTable);

    SeqUpdateExpression expression = new SeqUpdateExpression(symbolTable, seq, ind, exp);
    VariableExpression seqVar = expression.getSequenceVariableExpression();

    OperatorExpression size = new OperatorExpression(symbolTable, new Int(),
      UnaryOperator.Cardinality, List.of(seqVar));

    IntLiteral zero = new IntLiteral(new Int(), symbolTable, 0);
    OperatorExpression test = new OperatorExpression(symbolTable, new Bool(),
      BinaryOperator.Greater_Than, List.of(size, zero));

    IfElseExpression ifElseExpression = new IfElseExpression(symbolTable, type, test, expression,
      seqVar);

    return ifElseExpression;
  }

  private Expression generateSeqSubsequenceExpression(Type type, SymbolTable symbolTable) {
    Seq seqT = type.concrete(symbolTable).asSeq();
    Expression seq = generateExpression(seqT, symbolTable);

    Int indIT = new Int();
    Expression indI = generateExpression(indIT, symbolTable);

    Expression indJ;
    Int indJT = new Int();
    if (GeneratorConfig.getRandom().nextDouble() < PROB_HI_AND_LO_SUBSEQUENCE) {
      indJ = generateExpression(indJT, symbolTable);
    } else {
      indJ = new IntLiteral(indJT, symbolTable, 0);
    }
    SeqSubsequenceExpression expression = new SeqSubsequenceExpression(symbolTable, seq, indI,
      indJ);
    VariableExpression seqVar = expression.getSequenceVariableExpression();

    OperatorExpression size = new OperatorExpression(symbolTable, new Int(),
      UnaryOperator.Cardinality, List.of(seqVar));

    IntLiteral zero = new IntLiteral(new Int(), symbolTable, 0);
    OperatorExpression test = new OperatorExpression(symbolTable, new Bool(),
      BinaryOperator.Greater_Than, List.of(size, zero));

    IfElseExpression ifElseExpression = new IfElseExpression(symbolTable, type, test, expression,
      seqVar);

    return ifElseExpression;
  }

  private Expression generateDMapSelectionExpression(Type type, SymbolTable symbolTable) {
    DMap mapT = new DMap().setValueType(type).concrete(symbolTable).asDMap();
    Expression map = generateExpression(mapT, symbolTable);

    Type keyT = mapT.getKeyType();
    Expression ind = generateExpression(keyT, symbolTable);

    Expression def = generateExpression(type, symbolTable);

    DMapSelection dMapSelection = new DMapSelection(symbolTable, type, map, ind, def);
    return dMapSelection;
  }


  private Expression generateSeqIndexExpression(Type type, SymbolTable symbolTable) {
    Seq seqT = new Seq(type.concrete(symbolTable));
    Expression seq = generateExpression(seqT, symbolTable);

    Int indT = new Int();
    Expression ind = generateExpression(indT, symbolTable);
    Variable indVar = new Variable(
      VariableNameGenerator.generateVariableValueName(indT, symbolTable), indT);
    VariableExpression indVarExp = new VariableExpression(symbolTable, indVar, indT);

    Statement asStatIndPre = new AssignmentStatement(symbolTable, List.of(indVar), ind);

    SeqIndexExpression expression = new SeqIndexExpression(symbolTable, type, seq, indVar,
      asStatIndPre);

    VariableExpression seqVar = expression.getSequenceVariableExpression();

    OperatorExpression size = new OperatorExpression(symbolTable, new Int(),
      UnaryOperator.Cardinality, List.of(seqVar));

    IntLiteral zero = new IntLiteral(new Int(), symbolTable, 0);
    OperatorExpression testBiggerThanZero = new OperatorExpression(symbolTable, new Bool(),
      BinaryOperator.Greater_Than, List.of(size, zero));

    OperatorExpression testSmallerThanLength = new OperatorExpression(symbolTable, new Bool(),
      BinaryOperator.Less_Than, List.of(indVarExp, size));
    OperatorExpression testLengthBiggerThanZero = new OperatorExpression(symbolTable, new Bool(),
      BinaryOperator.Greater_Than, List.of(indVarExp, zero));

    OperatorExpression testP1 = new OperatorExpression(symbolTable, new Bool(), BinaryOperator.And,
      List.of(testBiggerThanZero, testSmallerThanLength));
    OperatorExpression test = new OperatorExpression(symbolTable, new Bool(), BinaryOperator.And,
      List.of(testP1, testLengthBiggerThanZero));

    Type defT = type.concrete(symbolTable);
    Expression def = generateExpression(defT, symbolTable);
    IfElseExpression ifElseExpression = new IfElseExpression(symbolTable, type, test, expression,
      def);

    return ifElseExpression;
  }

  private VariableExpression generateVariableExpression(Type type, SymbolTable symbolTable) {
    List<Variable> variables = symbolTable.getAllVariables(type);

    if (!variables.isEmpty()) {
      int index = GeneratorConfig.getRandom().nextInt(variables.size());
      Variable variable = variables.get(index);
      VariableExpression expression = new VariableExpression(symbolTable, variable, type);
      return expression;
    }
    return null;
  }

  private OperatorExpression generateOperatorExpression(Type type, SymbolTable symbolTable) {
    Operator operator = generateOperator(type);
    if (operator == null) {
      return null;
    }

    List<List<Type>> typeArgs = operator.getTypeArgs();
    int randType = GeneratorConfig.getRandom().nextInt(typeArgs.size());
    List<Type> types = typeArgs.get(randType);

    types = operator.concreteType(types, symbolTable, type);
    int prev = operator.restrictions();

    List<Expression> args = new ArrayList<>();
    for (Type t : types) {
      Expression arg = generateExpression(t, symbolTable);
      args.add(arg);
    }

    OperatorExpression expression = new OperatorExpression(symbolTable, type, operator, args);
    operator.restore(prev);

    return expression;
  }

  private IfElseExpression generateIfElseExpression(Type type, SymbolTable symbolTable) {
    Bool testT = new Bool();
    Expression test = generateExpression(testT, symbolTable);

    Type ifT = type.concrete(symbolTable);
    Expression ifExp = generateExpression(ifT, symbolTable);

    Type elseT = type.concrete(symbolTable);
    Expression elseExp = generateExpression(elseT, symbolTable);
    IfElseExpression expression = new IfElseExpression(symbolTable, type, test, ifExp, elseExp);

    return expression;
  }

  public Expression generateLiteral(Type type, SymbolTable symbolTable) {
    Expression expression = type.generateLiteral(symbolTable);
    return expression;
  }

  private Operator generateOperator(Type type) {
    List<Operator> ops = Arrays.stream(BinaryOperator.values()).collect(Collectors.toList());
    ops.addAll(Arrays.stream(UnaryOperator.values()).collect(Collectors.toList()));

    List<Operator> validOperators = ops.stream()
      .filter(x -> x.returnType(type))
      .collect(Collectors.toList());

    if (validOperators.size() > 0) {
      int randOp = GeneratorConfig.getRandom().nextInt(validOperators.size());
      return validOperators.get(randOp);
    }
    return null;
  }

  private Expression generateCallFunctionExpression(Type type, SymbolTable symbolTable) {
    if (!type.validForFunctionBody()) {
      return null;
    }
    RandomFunctionGenerator functionGenerator = new RandomFunctionGenerator();
    Function f = functionGenerator.generateFunction(type, symbolTable);

    if (f == null) {
      return null;
    }

    CallFunctionExpression expression = f.generateCall(symbolTable);
    return expression;
  }

  public CallMethodExpression generateCallMethodExpression(SymbolTable symbolTable,
    List<Type> returnTypes) {
    if (!returnTypes.stream().allMatch(Type::validMethodType)) {
      return null;
    }
    RandomMethodGenerator methodGenerator = new RandomMethodGenerator();

    int prevDepth = RandomStatementGenerator.loopDepth;
    RandomStatementGenerator.loopDepth = 0;
    Method m = methodGenerator.generateMethod(returnTypes, symbolTable);
    RandomStatementGenerator.loopDepth = prevDepth;

    if (m == null) {
      return null;
    }

    CallMethodExpression expression = m.generateCall(symbolTable);
    return expression;
  }
}
