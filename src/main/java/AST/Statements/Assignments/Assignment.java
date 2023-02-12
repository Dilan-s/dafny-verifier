package AST.Statements.Assignments;

import AST.Statements.Statement;
import AST.Statements.Type.Type;
import AST.StringUtils.Constants;
import java.util.List;
import java.util.Map;

public abstract class Assignment implements Statement {

    protected final String variableName;
    private final boolean printAssignment;

    protected Assignment(String variableName, boolean printAssignment) {
        this.variableName = variableName;
        this.printAssignment = printAssignment;
    }

    @Override
    public String printResult() {
        if (!printAssignment) {
            return "";
        }
        StringBuilder code = new StringBuilder();
        code.append(Constants.PRINT);
        code.append("\"Printing Variable ");
        code.append(variableName);
        code.append(" with value \"");
        code.append(Constants.ARGUMENT_SEPARATOR);
        code.append(variableName);
        code.append(Constants.ARGUMENT_SEPARATOR);
        code.append(Constants.PRINT_NEW_LINE);
        code.append(Constants.END_OF_LINE);
        return code.toString();
    }

}
