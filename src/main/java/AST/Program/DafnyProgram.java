package AST.Program;

import AST.Generator.GeneratorConfig;
import AST.Generator.RandomStatementGenerator;
import AST.Statements.Statement;
import AST.SymbolTable.Method.Method;
import AST.SymbolTable.Types.PrimitiveTypes.Void;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.Map;
import java.util.Random;

public class DafnyProgram {

  public final Random random;

  public DafnyProgram(long seed) {
    random = new Random(seed);
  }

  public DafnyProgram() {
    random = new Random();
  }

  public Method generateProgram() {

    GeneratorConfig.setRandom(random);
    RandomStatementGenerator randomStatementGenerator = new RandomStatementGenerator();
    Method main = new Method(new Void(), "Main");

    Method safe_division = SafeMethods.safe_division();
    main.addMethod(safe_division);

    Method safe_modulus = SafeMethods.safe_modulus();
    main.addMethod(safe_modulus);

    Method safe_index_seq = SafeMethods.safe_index_seq();
    main.addMethod(safe_index_seq);

    Method safe_subsequence = SafeMethods.safe_subsequence();
    main.addMethod(safe_subsequence);

    Method safe_min_max = SafeMethods.safe_min_max();
    main.addMethod(safe_min_max);

    Statement statement = randomStatementGenerator.generateBody(main, main.getSymbolTable());
    main.setBody(statement);

    return main;
  }

  public void baseTestCase(Method main) {
    String baseTestCase = main.toString();
    try {
      Path path = Paths.get("./tests");
      Files.createDirectories(path);
      FileWriter p = new FileWriter(String.format("%s/test.dfy", path.toAbsolutePath()));
      p.write(baseTestCase);
      p.close();
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  public void MetamorphicProgramGeneration(Method main) {
    List<String> programOptions = main.toOutput();
    try {
      Path path = Paths.get("./tests");
      Files.createDirectories(path);
      for (int i = 0; i < programOptions.size(); i++) {
        FileWriter p = new FileWriter(String.format("%s/test%d.dfy", path.toAbsolutePath(), i));
        p.write(programOptions.get(i));
        p.close();
      }
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  public void expectedOutput(Method main) {
    StringBuilder s = new StringBuilder();
    main.executeWithOutput(s);
    try {
      Path path = Paths.get("./outputs");
      Files.createDirectories(path);
      FileWriter p = new FileWriter(String.format("%s/expected.txt", path.toAbsolutePath()));
      p.write(s.toString());
      p.close();
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  public void minimizedTestCase(Method main) {
    String minimizedTestCase = main.minimizedTestCase();
    try {
      Path path = Paths.get("./tests-minimized");
      Files.createDirectories(path);
      FileWriter p = new FileWriter(String.format("%s/test-minimized.dfy", path.toAbsolutePath()));
      p.write(minimizedTestCase);
      p.close();
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  public void incorrectValidationTestCase(Method main) {
    String minimizedTestCase = main.minimizedTestCase();
    Map<String, String> incorrectAssert = main.invalidValidationTests();
    if (!incorrectAssert.isEmpty()) {
      int i = 0;
      for (Map.Entry<String, String> replacement : incorrectAssert.entrySet()) {
        String incorrectTest = minimizedTestCase.replace(replacement.getKey(),
          replacement.getValue());
        if (!minimizedTestCase.equals(incorrectTest)) {
          try {
            Path path = Paths.get("./tests-incorrect");
            Files.createDirectories(path);
            FileWriter p = new FileWriter(
              String.format("%s/test-incorrect-%d.dfy", path.toAbsolutePath(), i));
            p.write(incorrectTest);
            p.close();
          } catch (IOException e) {
            e.printStackTrace();
          }
          i++;
        }
      }
    }
  }
}
