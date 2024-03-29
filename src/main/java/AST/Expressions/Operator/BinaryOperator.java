package AST.Expressions.Operator;

import AST.Errors.SemanticException;
import AST.Expressions.Expression;
import AST.Generator.GeneratorConfig;
import AST.Generator.RandomTypeGenerator;
import AST.SymbolTable.Method.Method;
import AST.SymbolTable.SymbolTable.SymbolTable;
import AST.SymbolTable.Types.DCollectionTypes.DCollection;
import AST.SymbolTable.Types.DCollectionTypes.DSet;
import AST.SymbolTable.Types.DCollectionTypes.Multiset;
import AST.SymbolTable.Types.DCollectionTypes.Seq;
import AST.SymbolTable.Types.DMap.DMap;
import AST.SymbolTable.Types.PrimitiveTypes.BitVector;
import AST.SymbolTable.Types.PrimitiveTypes.Bool;
import AST.SymbolTable.Types.PrimitiveTypes.DString;
import AST.SymbolTable.Types.PrimitiveTypes.Int.Int;
import AST.SymbolTable.Types.PrimitiveTypes.Int.LimitedInt;
import AST.SymbolTable.Types.Type;
import AST.SymbolTable.Types.Variables.Variable;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

public enum BinaryOperator implements Operator {
  Equivalence("<==>", List.of(Args.BOOL_BOOL), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        Boolean lhsVB = (Boolean) lhsV;
        Boolean rhsVB = (Boolean) rhsV;
        return lhsVB == rhsVB;
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s <==> %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s <==> %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Implies("==>", List.of(Args.BOOL_BOOL), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        Boolean lhsVB = (Boolean) lhsV;
        Boolean rhsVB = (Boolean) rhsV;
        return !(lhsVB && !rhsVB);
      }
      return null;
    }
  },
  ReverseImplies("<==", List.of(Args.BOOL_BOOL), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        Boolean lhsVB = (Boolean) lhsV;
        Boolean rhsVB = (Boolean) rhsV;
        return !(!lhsVB && rhsVB);
      }
      return null;
    }
  },
  And("&&", List.of(Args.BOOL_BOOL), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        Boolean lhsVB = (Boolean) lhsV;
        Boolean rhsVB = (Boolean) rhsV;
        return lhsVB && rhsVB;
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s && %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s && %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Or("||", List.of(Args.BOOL_BOOL), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        Boolean lhsVB = (Boolean) lhsV;
        Boolean rhsVB = (Boolean) rhsV;
        return lhsVB || rhsVB;
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s || %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s || %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Equals("==",
    List.of(Args.INT_INT, Args.BOOL_BOOL, Args.CHAR_CHAR, Args.REAL_REAL, Args.DSTRING_DSTRING,
      Args.DSET_DSET, Args.MULTISET_MULTISET, Args.SEQ_SEQ, Args.DMAP_DMAP, Args.TUPLE_TUPLE,
      Args.DATATYPE_DATATYPE, Args.DSTRING_DSTRING, Args.BV_BV), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      Type type = lhsE.getTypes().get(0);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);
      if (lhsV != null && rhsV != null) {
        return type.equal(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s == %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s == %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Not_Equals("!=",
    List.of(Args.INT_INT, Args.BOOL_BOOL, Args.CHAR_CHAR, Args.REAL_REAL, Args.DSTRING_DSTRING,
      Args.DSET_DSET, Args.MULTISET_MULTISET, Args.SEQ_SEQ, Args.DMAP_DMAP, Args.TUPLE_TUPLE,
      Args.DATATYPE_DATATYPE, Args.DSTRING_DSTRING, Args.BV_BV), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      Type type = lhsE.getTypes().get(0);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);
      if (lhsV != null && rhsV != null) {
        return !type.equal(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s != %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s != %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Less_Than("<", List.of(Args.INT_INT, Args.REAL_REAL, Args.CHAR_CHAR, Args.DSET_DSET,
    Args.MULTISET_MULTISET, Args.SEQ_SEQ, Args.DSTRING_DSTRING, Args.BV_BV), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      Type type = lhsE.getTypes().get(0);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.lessThan(lhsV, rhsV);
      }
      return null;
    }
  },
  Less_Than_Or_Equal("<=", List.of(Args.INT_INT, Args.REAL_REAL, Args.CHAR_CHAR, Args.DSET_DSET,
    Args.MULTISET_MULTISET, Args.SEQ_SEQ, Args.DSTRING_DSTRING, Args.BV_BV), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      Type type = lhsE.getTypes().get(0);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.lessThanOrEqual(lhsV, rhsV);
      }
      return null;
    }
  },
  Greater_Than(">", List.of(Args.INT_INT, Args.REAL_REAL, Args.CHAR_CHAR, Args.DSET_DSET,
    Args.MULTISET_MULTISET, Args.BV_BV), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      Type type = lhsE.getTypes().get(0);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.greaterThan(lhsV, rhsV);
      }
      return null;
    }
  },
  Greater_Than_Or_Equal(">=",
    List.of(Args.INT_INT, Args.REAL_REAL, Args.CHAR_CHAR, Args.DSET_DSET,
      Args.MULTISET_MULTISET, Args.BV_BV), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      Type type = lhsE.getTypes().get(0);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.greaterThanOrEqual(lhsV, rhsV);
      }
      return null;
    }
  },
  Plus("+", List.of(Args.INT_INT, Args.BV_BV), List.of(new Int(), new BitVector())) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Type type = args.get(0).getTypes().get(0);
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        BigInteger sum = lhsVI.add(rhsVI);
        if (type.equals(new BitVector())) {
          BitVector t = type.asBitVector();
          Operator.mask(sum, t.getSize());
        }
        return sum;
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> ret = new ArrayList<>();
      Type concrete = expected.concrete(symbolTable);
      for (Type ignored : types) {
        ret.add(concrete);
      }
      return ret;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s + %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s + %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Minus("-", List.of(Args.INT_INT, Args.BV_BV), List.of(new Int(), new BitVector())) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Type type = args.get(0).getTypes().get(0);
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        BigInteger sub = lhsVI.subtract(rhsVI);
        if (type.equals(new BitVector())) {
          BitVector t = type.asBitVector();
          Operator.mask(sub, t.getSize());
        }
        return sub;
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> ret = new ArrayList<>();
      Type concrete = expected.concrete(symbolTable);
      for (Type ignored : types) {
        ret.add(concrete);
      }
      return ret;
    }
  },
  Times("*", List.of(Args.INT_INT, Args.BV_BV), List.of(new Int(), new BitVector())) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Type type = args.get(0).getTypes().get(0);
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        BigInteger mult = lhsVI.multiply(rhsVI);
        if (type.equals(new BitVector())) {
          BitVector t = type.asBitVector();
          Operator.mask(mult, t.getSize());
        }
        return mult;
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> ret = new ArrayList<>();
      Type concrete = expected.concrete(symbolTable);
      for (Type ignored : types) {
        ret.add(concrete);
      }
      return ret;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s * %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s * %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Divide("/", List.of(Args.INT_INT), new Int()) {
    @Override
    public boolean requiresSafe(List<Object> vals) {
      BigInteger denominator = (BigInteger) vals.get(1);
      return denominator.equals(BigInteger.ZERO);
    }

    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;

        BigInteger x = lhsVI;
        BigInteger y = rhsVI;

        BigInteger r = x.divide(y);

        if (x.compareTo(BigInteger.ZERO) < 0 && !r.multiply(y).equals(x)) {
          r = r.subtract(y.compareTo(BigInteger.ZERO) > 0 ? BigInteger.ONE
            : BigInteger.ONE.negate());
        }
        return r;
      }
      return null;
    }
  },
  Modulus("%", List.of(Args.INT_INT), new Int()) {
    @Override
    public boolean requiresSafe(List<Object> vals) {
      BigInteger denominator = (BigInteger) vals.get(1);
      return denominator.equals(BigInteger.ZERO);
    }

    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;

        BigInteger r = (BigInteger) Divide.apply(args, paramsMap);
        return lhsVI.subtract(r.multiply(rhsVI));
      }
      return null;
    }
  },
  Disjoint("!!", List.of(Args.DSET_DSET, Args.MULTISET_MULTISET), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DCollection type = lhsE.getTypes().get(0).asDCollection();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.disjoint(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s !! %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s !! %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  Union("+", List.of(Args.DSET_DSET, Args.MULTISET_MULTISET, Args.SEQ_SEQ),
    List.of(new DSet(), new Seq(), new Multiset())) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DCollection type = lhsE.getTypes().get(0).asDCollection();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.union(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable,
      Type expected) {
      List<Type> ret = new ArrayList<>();
      for (Type ignored : types) {
        ret.add(expected.concrete(symbolTable));
      }
      return ret;
    }
  },
  MapAdd("+", List.of(Args.DMAP_DMAP), new DMap()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DMap type = lhsE.getTypes().get(0).asDMap();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.add(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable,
      Type expected) {
      List<Type> ret = new ArrayList<>();
      for (Type ignored : types) {
        ret.add(expected.concrete(symbolTable));
      }
      return ret;
    }
  },
  MapDifference("-", List.of(Args.DMAP_DSET), new DMap()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DMap type = lhsE.getTypes().get(0).asDMap();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.remove(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> ret = new ArrayList<>();
      DMap map = expected.concrete(symbolTable).asDMap();
      ret.add(map);
      ret.add(new DSet(map.getKeyType()));
      return ret;
    }
  },
  Difference("-", List.of(Args.DSET_DSET, Args.MULTISET_MULTISET),
    List.of(new DSet(), new Multiset())) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DCollection type = lhsE.getTypes().get(0).asDCollection();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.difference(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable,
      Type expected) {
      List<Type> ret = new ArrayList<>();
      for (Type ignored : types) {
        ret.add(expected.concrete(symbolTable));
      }
      return ret;
    }
  },
  Intersection("*", List.of(Args.DSET_DSET, Args.MULTISET_MULTISET),
    List.of(new DSet(), new Multiset())) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DCollection type = lhsE.getTypes().get(0).asDCollection();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.intersection(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable,
      Type expected) {
      List<Type> ret = new ArrayList<>();
      for (Type ignored : types) {
        ret.add(expected.concrete(symbolTable));
      }
      return ret;
    }
  },
  MembershipMap("in", List.of(Args.DMAP), new Bool()) {
    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      RandomTypeGenerator typeGenerator = new RandomTypeGenerator();
      Type t = typeGenerator.generateEqualTypes(1, symbolTable).get(0);
      List<Type> ret = new ArrayList<>();
      ret.add(t);
      DMap map = types.get(0).asDMap();
      ret.add(map.setKeyType(t).concrete(symbolTable));
      return ret;
    }

    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DMap map = rhsE.getTypes().get(0).asDMap();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return map.contains(lhsV, rhsV);
      }
      return null;
    }
  },
  NotMembershipMap("!in", List.of(Args.DMAP), new Bool()) {
    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      RandomTypeGenerator typeGenerator = new RandomTypeGenerator();
      Type t = typeGenerator.generateEqualTypes(1, symbolTable).get(0);
      List<Type> ret = new ArrayList<>();
      ret.add(t);
      DMap map = types.get(0).asDMap();
      ret.add(map.setKeyType(t).concrete(symbolTable));
      return ret;
    }

    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DMap map = rhsE.getTypes().get(0).asDMap();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return !map.contains(lhsV, rhsV);
      }
      return null;
    }
  },
  Membership("in", List.of(Args.SEQ, Args.DSET, Args.MULTISET), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DCollection type = rhsE.getTypes().get(0).asDCollection();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return type.contains(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable,
      Type expected) {
      RandomTypeGenerator typeGenerator = new RandomTypeGenerator();
      Type t = typeGenerator.generateEqualTypes(1, symbolTable).get(0);
      List<Type> ret = new ArrayList<>();
      ret.add(t);
      DCollection collection = types.get(0).asDCollection();
      ret.add(collection.setInnerType(t));
      return ret;
    }
  },
  NotMembership("!in", List.of(Args.SEQ, Args.DSET, Args.MULTISET), new Bool()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);
      DCollection type = rhsE.getTypes().get(0).asDCollection();

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        return !type.contains(lhsV, rhsV);
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable,
      Type expected) {
      RandomTypeGenerator typeGenerator = new RandomTypeGenerator();
      Type t = typeGenerator.generateEqualTypes(1, symbolTable).get(0);
      List<Type> ret = new ArrayList<>();
      ret.add(t);
      DCollection collection = types.get(0).asDCollection();
      ret.add(collection.setInnerType(t));
      return ret;
    }
  },
  Concatenate("+", List.of(Args.DSTRING_DSTRING), new DString()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      Expression rhsE = args.get(1);
      Type t = rhsE.getTypes().get(0);
      Expression lhsE = args.get(0);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      return t.concatenate(lhsV, rhsV);
    }
  },
  AndBV("&", List.of(Args.BV_BV), new BitVector()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      BitVector type = args.get(0).getTypes().get(0).asBitVector();
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        Operator.mask(lhsVI.and(rhsVI), type.getSize());
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s & %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s & %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  OrBV("|", List.of(Args.BV_BV), new BitVector()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      BitVector type = args.get(0).getTypes().get(0).asBitVector();
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        Operator.mask(lhsVI.or(rhsVI), type.getSize());
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s | %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s | %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  XorBV("^", List.of(Args.BV_BV), new BitVector()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      BitVector type = args.get(0).getTypes().get(0).asBitVector();
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        Operator.mask(lhsVI.xor(rhsVI), type.getSize());
      }
      return null;
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("(%s ^ %s)", l, r));
        }
      }

      for (String l : args.get(1).toOutput()) {
        for (String r : args.get(0).toOutput()) {
          res.add(String.format("(%s ^ %s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  ShiftLeft("<<", List.of(Args.BV_INT), new BitVector()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      BitVector type = args.get(0).getTypes().get(0).asBitVector();
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        Operator.mask(lhsVI.shiftLeft(rhsVI.intValueExact()), type.getSize());
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> res = new ArrayList<>();
      BitVector bv = expected.asBitVector();
      res.add(bv);
      res.add(new LimitedInt(bv.getSize()));
      return super.concreteType(types, symbolTable, expected);
    }
  },
  ShiftRight(">>", List.of(Args.BV_INT), new BitVector()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      BitVector type = args.get(0).getTypes().get(0).asBitVector();
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;
        return Operator.mask(lhsVI.shiftRight(rhsVI.intValueExact()), type.getSize());
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> res = new ArrayList<>();
      BitVector bv = expected.asBitVector();
      res.add(bv);
      res.add(new LimitedInt(bv.getSize()));
      return res;
    }
  },
  RotateLeft(".RotateLeft", List.of(Args.BV_INT), new BitVector()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      BitVector type = args.get(0).getTypes().get(0).asBitVector();
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        Integer size = type.getSize();
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;

        BigInteger upperBits = lhsVI.shiftLeft(rhsVI.intValueExact());
        BigInteger lowerBits = lhsVI.shiftRight(size - rhsVI.intValueExact());
        return Operator.mask(upperBits.add(lowerBits), type.getSize());
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> res = new ArrayList<>();
      BitVector bv = expected.asBitVector();
      res.add(bv);
      res.add(new LimitedInt(bv.getSize()));
      return res;
    }

    @Override
    public String formExpression(List<Expression> args) {
      return String.format("%s.RotateLeft(%s)", args.get(0), args.get(1));
    }

    @Override
    public String formMinimizedExpression(List<Expression> args) {
      return String.format("%s.RotateLeft(%s)", args.get(0).minimizedTestCase(), args.get(1).minimizedTestCase());
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("%s.RotateLeft(%s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  },
  RotateRight(".RotateRight", List.of(Args.BV_INT), new BitVector()) {
    @Override
    public Object apply(List<Expression> args, Map<Variable, Variable> paramsMap) {
      BitVector type = args.get(0).getTypes().get(0).asBitVector();
      Expression lhsE = args.get(0);
      Expression rhsE = args.get(1);

      Object lhsV = lhsE.getValue(paramsMap).get(0);
      Object rhsV = rhsE.getValue(paramsMap).get(0);

      if (lhsV != null && rhsV != null) {
        Integer size = type.getSize();
        BigInteger lhsVI = (BigInteger) lhsV;
        BigInteger rhsVI = (BigInteger) rhsV;

        BigInteger lowerBits = lhsVI.shiftRight(rhsVI.intValueExact());
        BigInteger upperBits = lhsVI.shiftLeft(size - rhsVI.intValueExact());
        return Operator.mask(upperBits.add(lowerBits), type.getSize());
      }
      return null;
    }

    @Override
    public List<Type> concreteType(List<Type> types, SymbolTable symbolTable, Type expected) {
      List<Type> res = new ArrayList<>();
      BitVector bv = expected.asBitVector();
      res.add(bv);
      res.add(new LimitedInt(bv.getSize()));
      return res;
    }

    @Override
    public String formExpression(List<Expression> args) {
      return String.format("%s.RotateRight(%s)", args.get(0), args.get(1));
    }

    @Override
    public String formMinimizedExpression(List<Expression> args) {
      return String.format("%s.RotateRight(%s)", args.get(0).minimizedTestCase(), args.get(1).minimizedTestCase());
    }

    @Override
    public List<String> formOutput(List<Expression> args) {
      Set<String> res = new HashSet<>();

      for (String l : args.get(0).toOutput()) {
        for (String r : args.get(1).toOutput()) {
          res.add(String.format("%s.RotateRight(%s)", l, r));
        }
      }

      List<String> r = new ArrayList<>(res);
      Collections.shuffle(r, GeneratorConfig.getRandom());
      return r.subList(0, Math.min(5, res.size()));
    }
  };

  private final String operator;
  private final List<List<Type>> typeArgs;
  private final List<Type> retTypes;

  BinaryOperator(String operator, List<List<Type>> typeArgs, Type retType) {
    this.operator = operator;
    this.typeArgs = typeArgs;
    this.retTypes = List.of(retType);
  }

  BinaryOperator(String operator, List<List<Type>> typeArgs, List<Type> retType) {
    this.operator = operator;
    this.typeArgs = typeArgs;
    this.retTypes = retType;
  }

  @Override
  public String formExpression(List<Expression> args) {
    String res = args.get(0).toString();
    for (int i = 1; i < args.size(); i++) {
      Expression rhs = args.get(i);
      res = String.format("(%s %s %s)", res, operator, rhs.toString());

    }
    return res;
  }

  @Override
  public String formMinimizedExpression(List<Expression> args) {
    String res = args.get(0).minimizedTestCase();
    for (int i = 1; i < args.size(); i++) {
      Expression rhs = args.get(i);
      res = String.format("(%s %s %s)", res, operator, rhs.minimizedTestCase());

    }
    return res;
  }

  @Override
  public List<String> formOutput(List<Expression> args) {
    List<String> res = new ArrayList<>();

    for (String l : args.get(0).toOutput()) {
      for (String r : args.get(1).toOutput()) {
        res.add(String.format("(%s %s %s)", l, operator, r));
      }
    }

    List<String> r = new ArrayList<>(res);
    Collections.shuffle(r, GeneratorConfig.getRandom());
    return r.subList(0, Math.min(5, res.size()));
  }

  @Override
  public List<Type> getType() {
    return retTypes;
  }

  @Override
  public void semanticCheck(Method method, List<Expression> expressions)
    throws SemanticException {
  }

  @Override
  public List<List<Type>> getTypeArgs() {
    return typeArgs;
  }

  public int getNumberOfArgs() {
    return 2;
  }
}
