package middleend;

import frontend.Node;
import frontend.symbol.SymbolEngine;
import frontend.symbol.Symbol;

import java.io.IOException;
import java.io.PrintWriter;
import java.io.File;
import java.util.*;
import java.util.Stack;

public class LLVMIRGenerator{
    private Node root;
    private SymbolEngine symbolEngine;
    private StringBuilder irBuilder;
    private Map<String, String> globalVars;
    private Map<String, String> localVars;
    private Map<emm, NewDef> hhh; // name to name
    private List<ConstString> constStrings = new ArrayList<>();
    private int scopeCounter;
    Stack<Integer> scope;
    private int tempCounter;
    private int labelCounter;
    private int stringLiteralCounter;
    private int stringConstPos;
    private String table;

    private Stack<String> breakLabels = new Stack<>();
    private Stack<String> continueLabels = new Stack<>();

    private static final String STRING_PLACEHOLDER = "; <strings placeholder>\n\n";
    private static final String STATIC_PLACEHOLDER = "; <static placeholder>\n\n";
    private static final Map<String, String> TYPE_MAP = new HashMap<>();
    static {
        TYPE_MAP.put("Int", "i32");
        TYPE_MAP.put("IntArray", "i32*");
        TYPE_MAP.put("ConstInt", "i32");
        TYPE_MAP.put("ConstIntArray", "i32*");
        TYPE_MAP.put("StaticInt", "i32");
        TYPE_MAP.put("StaticIntArray", "i32*");
        TYPE_MAP.put("VoidFunc", "void");
        TYPE_MAP.put("IntFunc", "i32");
    }

    public LLVMIRGenerator() {
        this.globalVars = new HashMap<>();
        this.localVars = new HashMap<>();
        this.tempCounter = 0;
        this.labelCounter = 0;
//        this.stringLiterals = new LinkedHashMap<>();
        this.stringLiteralCounter = 0;
        this.stringConstPos = -1;
        this.hhh = new HashMap<>();
        this.scopeCounter = 0;
        this.scope = new Stack<>();
        scope.push(0);
        this.table = "";
    }

    private void enter() {
        scope.push(++scopeCounter);
        if (scope.size() > 1) table = "    ";
    }

    private void exit() {
        scope.pop();
        if (scope.size() == 1) table = "";
    }

    private int curScope() {
        return scope.peek();
    }

    public String generate(Node root, SymbolEngine symbolEngine) {
        this.root = root;
        this.symbolEngine = symbolEngine;
        this.irBuilder = new StringBuilder();
        this.tempCounter = 0;
        this.labelCounter = 0;
//        this.stringLiterals.clear();
        this.stringLiteralCounter = 0;
        this.stringConstPos = -1;
//        this.blockTerminated = false;

        generateModuleDeclaration();
        generateGlobalVariables();
        generateFunctions();

        insertStringLiterals();
        insertStaticVar();

        return irBuilder.toString();
    }

    private void insertStringLiterals() {
        if (stringConstPos < 0) return;
        String placeholder = STRING_PLACEHOLDER;
        irBuilder.delete(stringConstPos, stringConstPos + placeholder.length());
        if (constStrings.isEmpty()) return;
        StringBuilder decls = new StringBuilder();
        for (ConstString x : constStrings) {
            decls.append(x.name)
                    .append(" = constant [")
                    .append(x.len).append(" x i8] c")
                    .append("\"" + x.value + "\"" + "\n");
        }
        decls.append("\n");
        irBuilder.insert(stringConstPos, decls);
    }

    private List<String> staticVars = new ArrayList<>();
    private void insertStaticVar() {
        String placeholder = STATIC_PLACEHOLDER;
        int staticVarPos = irBuilder.toString().indexOf(placeholder);
        if (staticVarPos < 0) return;
        irBuilder.delete(staticVarPos, staticVarPos + placeholder.length());
        if (staticVars.isEmpty()) return;
        StringBuilder decls = new StringBuilder();
        for (String x : staticVars) decls.append(x);
        decls.append("\n");
        irBuilder.insert(staticVarPos, decls);
    }

    private void generateModuleDeclaration() {
        irBuilder.append("declare i32 @getint()\n");
        irBuilder.append("declare void @putint(i32)\n");
        irBuilder.append("declare void @putstr(i8*)\n\n");

        // <string newFuncdef>
        NewFuncDef getint = new NewFuncDef("getint",
                1, new ArrayList<>());
        NewFuncDef putint = new NewFuncDef("putint",
                0, new ArrayList<>(Arrays.asList("i32")));
        NewFuncDef putstr = new NewFuncDef("putstr",
                0, new ArrayList<>(Arrays.asList("i8*")));
        functionNameMap.put("getint", getint);
        functionNameMap.put("putint", putint);
        functionNameMap.put("putstr", putstr);

        this.stringConstPos = irBuilder.length();
        irBuilder.append(STRING_PLACEHOLDER);

        irBuilder.append(STATIC_PLACEHOLDER);
    }

    private void generateGlobalVariables() {
        for (Node child : root.getSons()) {
            if (child.isType("Decl"))
                processGlobalDecl(child);
        }
        irBuilder.append("\n");
    }

    private void processGlobalDecl(Node declNode) {
        for (Node child : declNode.getSons()) {
            if (child.isType("ConstDecl") || child.isType("VarDecl")) {
                processGlobalVarDecl(child);
            }
        }
    }

    // ConstDecl → 'const' BType ConstDef { ',' ConstDef } ';'
    // VarDecl → [ 'static' ] BType VarDef { ',' VarDef } ';'
    private void processGlobalVarDecl(Node varDeclNode) {
        for (Node child : varDeclNode.getSons()) {
            if (child.isType("ConstDef") || child.isType("VarDef")) {
                processGlobalDef(child, null);
            }
        }
    }

    private int globalDefCounter = 0;
    private int functionCounter = 0;
    private Map<String, NewFuncDef> functionNameMap = new HashMap<>();

    private NewFuncDef getRealFunc(String name) {
        if (functionNameMap.containsKey(name)) return functionNameMap.get(name);
        return null;
    }
    private String newFunctionName() {
        return "f" + (functionCounter++);
    }
    private String newGlobalName() {
        return "@g" + (globalDefCounter++);
    }
    private String newTemp() {
        return "%t" + (tempCounter++);
    }
    // has a symbol on the node
    // ConstDef → Ident [ '[' ConstExp ']' ] '=' ConstInitVal
    // VarDef → Ident [ '[' ConstExp ']' ] | Ident [ '[' ConstExp ']' ] '=' InitVal
    private void processGlobalDef(Node defNode, String uu) {
        Symbol sb = defNode.symbol;
        String name = sb.name;
        String realName = uu == null ? newGlobalName() : uu;
        StringBuilder tmpsb = new StringBuilder();

        if (sb.isArray) {
            int size = sb.getArraySize();
            hhh.put(new emm(name, curScope()), new NewDef(realName, size, 1));
            String type = "[" + size + " x i32]";
            String keyword = "global";
            globalVars.put(realName, type);
            String initializer = generateArrayInitializer(sb.arrayValues);

            tmpsb.append(realName).append(" = ").append(keyword)
                    .append(" ").append(type).append(" ")
                    .append(initializer).append("\n");
        } else {
            hhh.put(new emm(name, curScope()), new NewDef(realName, -1, 1));
            String keyword = "global";
            globalVars.put(realName, "i32");
            tmpsb.append(realName) .append(" = ").append(keyword)
                    .append(" i32 ").append(sb.getValue()).append("\n");
        }
        if (uu == null) irBuilder.append(tmpsb);
        else staticVars.add(tmpsb.toString());
    }

    private String generateArrayInitializer(List<Integer> values) {
        StringBuilder sb = new StringBuilder("[");
        int len = values.size();
        for (int i = 0; i < len; i++) {
            sb.append("i32 ");
            sb.append(values.get(i));
            if (i < len - 1) {
                sb.append(", ");
            }
        }
        sb.append("]");
        return sb.toString();
    }

    ///////////////////////////////////// first part

    private int evaluateConstExp(Node constExp) {
        // ConstExp → AddExp
        return evaluateAddExp(constExp.getSon("AddExp"));
    }

    private int evaluateAddExp(Node addExp) {
        // AddExp → MulExp | AddExp ('+' | '−') MulExp
        if (addExp.getSons().size() == 1) {
            return evaluateMulExp(addExp.getSon("MulExp"));
        } else {
            Node left = addExp.getSon("AddExp");
            Node op = addExp.getSons().get(1);
            Node right = addExp.getSon("MulExp");

            int leftVal = evaluateAddExp(left);
            int rightVal = evaluateMulExp(right);

            if (op.getToken().getType().equals("PLUS")) {
                return leftVal + rightVal;
            } else {
                return leftVal - rightVal;
            }
        }
    }

    private int evaluateMulExp(Node mulExp) {
        // MulExp → UnaryExp | MulExp ('*' | '/' | '%') UnaryExp
        if (mulExp.getSons().size() == 1) {
            return evaluateUnaryExp(mulExp.getSon("UnaryExp"));
        } else {
            Node left = mulExp.getSon("MulExp");
            Node op = mulExp.getSons().get(1);
            Node right = mulExp.getSon("UnaryExp");

            int leftVal = evaluateMulExp(left);
            int rightVal = evaluateUnaryExp(right);

            if (op.getToken().getType().equals("MULT")) {
                return leftVal * rightVal;
            } else if (op.getToken().getType().equals("DIV")) {
                return leftVal / rightVal;
            } else {
                return leftVal % rightVal;
            }
        }
    }

    private int evaluateUnaryExp(Node unaryExp) {
        // UnaryExp → PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp UnaryExp
        if (unaryExp.getSons().size() == 1) {
            return evaluatePrimaryExp(unaryExp.getSon("PrimaryExp"));
        } else if (unaryExp.getSon("UnaryOp") != null) {
            Node unaryOp = unaryExp.getSon("UnaryOp");
            Node operand = unaryExp.getSons().get(1);

            int operandVal = evaluateUnaryExp(operand);

            if (unaryOp.getToken().getType().equals("PLUS")) {
                return operandVal;
            } else if (unaryOp.getToken().getType().equals("MINU")) {
                return -operandVal;
            } else {
                return operandVal == 0 ? 1 : 0; // NOT operation
            }
        } else {
            // Function call, not supported in constant expression
            return 0;
        }
    }

    private int evaluatePrimaryExp(Node primaryExp) {
        // PrimaryExp → '(' Exp ')' | LVal | Number
        if (primaryExp.getSon("Number") != null) {
            return Integer.parseInt(primaryExp.getSon("Number").getSon("INTCON").getToken().getValue());
        } else if (primaryExp.getSon("LVal") != null) {
            // LVal → Ident ['[' Exp ']']
            Node lVal = primaryExp.getSon("LVal");
            String varName = lVal.getDefName();

            Symbol symbol = symbolEngine.getManager().get(varName);
            if (symbol != null && symbol.isConst) {
                if (symbol.isArray) {
                    // 常量数组元素访问
                    Node indexExp = null;
                    for (Node child : lVal.getSons()) {
                        if (child.isType("Exp")) {
                            indexExp = child;
                            break;
                        }
                    }

                    if (indexExp != null) {
                        int index = evaluateConstExp(indexExp);
                        List<Integer> arrayValues = symbol.getArrayValues();
                        if (arrayValues != null && index >= 0 && index < arrayValues.size()) {
                            return arrayValues.get(index);
                        }
                    }
                    return 0;
                } else {
                    // 常量变量
                    return symbol.getValue();
                }
            }
            // Can't evaluate non-constant variables
            return 0;
        } else {
            // '(' Exp ')'
            return evaluateAddExp(primaryExp.getSon("Exp").getSon("AddExp"));
        }
    }

    private void generateFunctions() {
        for (Node child : root.getSons()) {
            if (child.isType("FuncDef")) {
                generateFunction(child);
            } else if (child.isType("MainFuncDef")) {
                generateMainFunction(child);
            }
        }
    }

    private boolean hasReturn = false;
    // FuncDef → FuncType Ident '(' [FuncFParams] ')' Block
    private void generateFunction(Node funcDefNode) {
        this.enter();
        Symbol sb = funcDefNode.symbol;
        String funcName = sb.name;
        localVars.clear();
        String realName = newFunctionName();
        this.hasReturn = false;
        String returnType = "i32";
        for (Node child : funcDefNode.getSons()) {
            if (child.isType("FuncType")) {
                Node typeNode = child.getSons().get(0);
                if (typeNode.isType("VOIDTK")) {
                    returnType = "void";
                }
                break;
            }
        }
        this.curFuncType = returnType;
        functionNameMap.put(funcName, new NewFuncDef
                (realName, returnType.equals("void") ? 0 : 1, sb.paramTypes));

        irBuilder.append("define ").append(returnType)
                .append(" @").append(realName).append("(");

        Node funcFParams = funcDefNode.getSon("FuncFParams");
        if (funcFParams != null) {
            processFunctionParams(funcFParams, sb.paramTypes);
        }

        irBuilder.append(") {\n");
        irBuilder.append("entry_").append(realName).append(":\n");
        Node block = funcDefNode.getSon("Block");
        if (block != null) {
            generateBlock(block, false);
        }

        if (returnType.equals("void")) {
            irBuilder.append(table + "ret void").append("\n");
        }
        irBuilder.append("}\n\n");
        this.exit();
    }

    private void generateMainFunction(Node mainFuncDefNode) {
        this.enter();
        localVars.clear();

        irBuilder.append("define i32 @main() {\n");
        irBuilder.append("entry_main:\n");
        this.curFuncType = "i32";

        Node block = mainFuncDefNode.getSon("Block");
        if (block != null)
            generateBlock(block, true);

        irBuilder.append("}\n\n");
        this.exit();
    }

    private void processFunctionParams(Node funcFParams, List<String> paramTypes) {
        boolean first = true;
        // FuncFParams → FuncFParam { ',' FuncFParam }
        // FuncFParam → BType Ident ['[' ']']
        int i = 0;
        for (Node child : funcFParams.getSons()) {
            if (child.isType("FuncFParam")) {
                String paramName = child.getDefName();
                String realName = newTemp();
                boolean isArray = paramTypes.get(i).equals("IntArray");
                ++i;
                String paramType = isArray ? "i32*" : "i32";
                if (!first) irBuilder.append(", ");
                first = false;

                irBuilder.append(paramType).append(" ").append(realName);
                hhh.put(new emm(paramName, curScope()),
                        new NewDef(realName, -1, (isArray) ? 1 : 0, true));
            }
        }
    }

    private void generateBlock(Node block, boolean okk) {
        if (okk) enter();
        for (Node child : block.getSons()) {
            if (child.isType("BlockItem")) {
                generateBlockItem(child);
            }
        }
        if (okk) exit();
    }

    //  BlockItem → Decl | Stmt
    private void generateBlockItem(Node blockItem) {
        for (Node child : blockItem.getSons()) {
            if (child.isType("Decl")) {
                processLocalDecl(child);
            } else if (child.isType("Stmt")) {
                generateStmt(child);
            }
        }
    }

    //  Decl → ConstDecl | VarDecl
    private void processLocalDecl(Node declNode) {
        Node x = declNode.getSons().get(0);
        // ConstDecl → 'const' BType ConstDef { ',' ConstDef } ';'
        // VarDecl → [ 'static' ] BType VarDef { ',' VarDef } ';'
        for (Node child : x.getSons()) {
            if (child.isType("ConstDef") || child.isType("VarDef")) {
                processLocalDef(child);
            }
        }
    }

    private void processLocalDef(Node defNode) {
        Symbol sb = defNode.symbol;
        String varName = sb.name;
        boolean isArray = sb.isArray;
        boolean isSta = sb.isStatic;
        String realName = newTemp();
        if (isSta) {
            realName = "@" + realName.substring(1);
            realName = realName.replace("t", "gg");
            processGlobalDef(defNode, realName);
            return;
        }

        // VarDef → Ident [ '[' ConstExp ']' ] | Ident [ '[' ConstExp ']' ] '=' InitVal
        // ConstDef → Ident [ '[' ConstExp ']' ] '=' ConstInitVal
        if (isArray) {
            int size = sb.getArraySize();
            hhh.put(new emm(varName, curScope()), new NewDef(realName, size, 1));
            String type = "[" + size + " x i32]";
            irBuilder.append(table).append(realName).append(" = alloca ")
                    .append(type).append("\n");
            if (defNode.hasSon("ASSIGN", -1)) {
                if (sb.isConst) {
                    /*
                %v10 = getelementptr inbounds [4 x i32], [4 x i32]* %v9, i32 0, i32 1
	            store i32 1, i32* %v10
                     */
                    List<Integer> arrayValues = sb.getArrayValues();
                    for (int i = 0; i < sb.lim; ++i) {
                        int value = arrayValues.get(i);
                        String ptr = newTemp();
                        getElemPtr(ptr, size, realName, String.valueOf(i));
                        irBuilder.append(table).append("store i32 ")
                                .append(value).append(", i32* ").append(ptr).append("\n");
                    }
                } else {
                    Node initVal = defNode.getSon("InitVal");
                    int cc = 0;
                    for (Node x : initVal.getSons()) if (x.isType("Exp")) {
                        String value = generateExp(x);
                        String ptr = newTemp();
                        getElemPtr(ptr, size, realName, String.valueOf(cc));
                        irBuilder.append(table).append("store i32 ")
                                .append(value).append(", i32* ").append(ptr).append("\n");
                        ++cc;
                    }
                }
            }
        } else {
            hhh.put(new emm(varName, curScope()), new NewDef(realName, -1, 1));
            irBuilder.append(table).append(realName).append(" = alloca i32\n");
            if (sb.isConst) {
                int value = sb.getValue();
                irBuilder.append(table + "store i32 ").append(value)
                        .append(", i32* ").append(realName).append("\n");
            } else {
                Node initVal = defNode.getSon("InitVal");
                if (initVal != null) {
                    String value = generateExp(initVal.getSon("Exp"));
                    irBuilder.append(table + "store i32 ").append(value)
                            .append(", i32* ").append(realName).append("\n");
                }
            }
        }
    }

    /*
    Stmt → LVal '=' Exp ';' // h
        | [Exp] ';'
        | Block
        | 'if' '(' Cond ')' Stmt [ 'else' Stmt ]
        | 'for' '(' [ForStmt] ';' [Cond] ';' [ForStmt] ')' Stmt // h
        | 'break' ';' | 'continue' ';' // m
        | 'return' [Exp] ';' // f
        | 'printf''('StringConst {','Exp}')'';' // l
     */
    private void generateStmt(Node stmt) {
        Node firstChild = stmt.getSons().get(0);

        if (firstChild.isType("LVal")) {
            generateAssignStmt(stmt);
        } else if (firstChild.isType("Exp") || firstChild.isType("SEMICN")) {
            if (firstChild.isType("Exp")) {
                generateExp(firstChild);
            }
        } else if (firstChild.isType("Block")) {
            generateBlock(firstChild, true);
        } else if (firstChild.isType("IFTK")) {
            generateIfStmt(stmt);
        } else if (firstChild.isType("FORTK")) {
            generateFor(stmt);
        } else if (firstChild.isType("BREAKTK")) {
            if (!breakLabels.isEmpty()) {
                irBuilder.append(table + "br label %").append(breakLabels.peek()).append("\n");
            }
        } else if (firstChild.isType("CONTINUETK")) {
            if (!continueLabels.isEmpty()) {
                irBuilder.append(table + "br label %").append(continueLabels.peek()).append("\n");
            }
        } else if (firstChild.isType("RETURNTK")) {
            generateReturnStmt(stmt);
        } else if (firstChild.isType("PRINTFTK")) {
            generatePrintfStmt(stmt);
        }
    }


    private void getElemPtr(String result, int size, String arrayPtr, String index) {
        if (size > 0) {
            irBuilder.append(table).append(result).append(" = getelementptr inbounds [").append(size)
                    .append(" x i32], [").append(size).append(" x i32]* ").append(arrayPtr)
                    .append(", i32 0, i32 ").append(index).append("\n");
        } else {
            irBuilder.append(table).append(result).append(" = getelementptr inbounds i32, i32* ")
                    .append(arrayPtr).append(", i32 ").append(index).append("\n");
        }

    }
    // Stmt → LVal '=' Exp ';'
    private void generateAssignStmt(Node stmt) {
        Node lVal = stmt.getSon("LVal");
        Node exp = stmt.getSon("Exp");

        if (lVal != null && exp != null) {
            String varName = lVal.getDefName();
            String value = generateExp(exp);
            NewDef def = getRealName(varName);
            if (lVal.hasSon("LBRACK", -1)) {
                Node indexExp = lVal.getSon("Exp");

                if (indexExp != null) {
                    String index = generateExp(indexExp);
                    String ptr = newTemp();
                    String arrayPtr = def.name;
                    int elementSize = def.size;
                    getElemPtr(ptr, elementSize, arrayPtr, index);
                    irBuilder.append(table + "store i32 ").append(value)
                            .append(", i32* ").append(ptr).append("\n");
                }
            } else {
                String ptr = def.name;
                if (def.type == 0) {
                    String realPtr = newTemp();
                    addPointer(realPtr);
                    irBuilder.append(table + "store i32 ").append(value)
                            .append(", i32* ").append(realPtr).append("\n");
                    hhh.remove(new emm(varName, curScope()));
                    hhh.put(new emm(varName, curScope()),
                            new NewDef(realPtr, -1, 1));
                }
                else {
                    irBuilder.append(table + "store i32 ").append(value)
                            .append(", i32* ").append(ptr).append("\n");
                }
            }
        }
    }

    private String generateExp(Node exp) {
        // Exp → AddExp
        return generateAddExp(exp.getSon("AddExp"));
    }

    /*
        %v19 = load i32, i32* %v17
        %v20 = load i32, i32* %v14
        %v21 = add i32 %v19, %v20
        store i32 %v21, i32* %v18
        %v22 = load i32, i32* %v15
     */
    private String generateAddExp(Node addExp) {
        // AddExp → MulExp | AddExp ('+' | '−') MulExp
        if (addExp.getSons().size() == 1) {
            return generateMulExp(addExp.getSon("MulExp"));
        } else {
            String left = generateAddExp(addExp.getSon("AddExp"));
            String right = generateMulExp(addExp.getSon("MulExp"));
            String op = addExp.getSons().get(1).getToken().getType();
            String result = newTemp();

            if (op.equals("PLUS")) {
                irBuilder.append(table).append(result).append(" = add i32 ").append(left).append(", ").append(right).append("\n");
            } else {
                irBuilder.append(table).append(result).append(" = sub i32 ").append(left).append(", ").append(right).append("\n");
            }
            return result;
        }
    }

    private String generateMulExp(Node mulExp) {
        // MulExp → UnaryExp | MulExp ('*' | '/' | '%') UnaryExp
        if (mulExp.getSons().size() == 1) {
            return generateUnaryExp(mulExp.getSon("UnaryExp"));
        } else {
            String left = generateMulExp(mulExp.getSon("MulExp"));
            String right = generateUnaryExp(mulExp.getSon("UnaryExp"));
            String op = mulExp.getSons().get(1).getToken().getType();
            String result = newTemp();

            if (op.equals("MULT")) {
                irBuilder.append(table).append(result).append(" = mul i32 ").append(left).append(", ").append(right).append("\n");
            } else if (op.equals("DIV")) {
                irBuilder.append(table).append(result).append(" = sdiv i32 ").append(left).append(", ").append(right).append("\n");
            } else {
                irBuilder.append(table).append(result).append(" = srem i32 ").append(left).append(", ").append(right).append("\n");
            }

            return result;
        }
    }

    private String generateUnaryExp(Node unaryExp) {
        // UnaryExp → PrimaryExp | Ident '(' [FuncRParams] ')' | UnaryOp UnaryExp
        if (unaryExp.getSons().size() == 1) {
            return generatePrimaryExp(unaryExp.getSon("PrimaryExp"));
        } else if (unaryExp.getSon("UnaryOp") != null) {
            Node unaryOp = unaryExp.getSon("UnaryOp");
            Node operand = unaryExp.getSons().get(1);

            String operandVal = generateUnaryExp(operand);
            String result = newTemp();
            Node opTypeNode = unaryOp.getSons().get(0);

            if (opTypeNode.isType("PLUS")) {
                // No operation needed
                return operandVal;
            } else if (opTypeNode.isType("MINU")) {
                irBuilder.append(table).append(result).append(" = sub i32 0, ").append(operandVal).append("\n");
            } else {
                // NOT operation
                irBuilder.append(table).append(result).append(" = icmp eq i32 ").append(operandVal).append(", 0\n");
                String boolResult = newTemp();
                irBuilder.append(table).append(boolResult).append(" = zext i1 ").append(result).append(" to i32\n");
                return boolResult;
            }
            return result;
        } else {
            // Function call: Ident '(' [FuncRParams] ')'
            return generateFunctionCall(unaryExp);
        }
    }

    private String generatePrimaryExp(Node primaryExp) {
        // PrimaryExp → '(' Exp ')' | LVal | Number
        if (primaryExp.getSon("Number") != null) {
            return primaryExp.getSon("Number").getSon("INTCON").getToken().getValue();
        } else if (primaryExp.getSon("LVal") != null) {
            return generateLVal(primaryExp.getSon("LVal"));
        } else {
            // '(' Exp ')'
            return generateExp(primaryExp.getSon("Exp"));
        }
    }

    private NewDef getRealName(String varName) {
        for (int i = scope.size() - 1; i >= 0; --i) {
            emm em = new emm(varName, scope.get(i));
            if (hhh.containsKey(em)) return hhh.get(em);
        }
        return null;
    }

    private void addPointer(String name) {
        irBuilder.append(table + name).append(" = alloca i32\n");
    }
    private void storeValue(String value, String ptr) {
        irBuilder.append(table).append("store i32 ").append(value).append(", i32* ").append(ptr).append("\n");
    }
    private String generateLVal(Node lVal) {
        // LVal → Ident ['[' Exp ']']
        String varName = lVal.getDefName();
        boolean isArrayAccess = lVal.hasSon("LBRACK", -1);
        String result = newTemp();

        if (!isArrayAccess) {
            /*
                %v1 = alloca i32
                store i32 %v0, i32* %v1
            */
            NewDef uu = getRealName(varName);
            String ptr = uu.name;
            int type = uu.type;
            if (isFuncRParams && (uu.size > 0 || uu.isParam)) {
                getElemPtr(result, uu.size, ptr, "0");
                return result;
            }
            else if (type == 0) {
                return ptr;
                /*
//                String tmp = newTemp();
//                addPointer(tmp);
//                storeValue(ptr, tmp);
//                irBuilder.append(table + result).append(" = load i32, i32* ").append(tmp).append("\n");
//                return result;
                */
            }
            else {
                irBuilder.append(table).append(result).
                        append(" = load i32, i32* ").append(ptr).append("\n");
                return result;
            }

        } else {
            // Array element access
            String ptr = newTemp();
            NewDef tt = getRealName(varName);
            if (tt == null) return "0";
            Node indexExp = lVal.getSon("Exp");
            if(indexExp == null) return "0";
            String index = generateExp(indexExp);
            String realName = tt.name;
            int size = tt.size;
            /*
            %v1 = getelementptr inbounds [5 x i32], [5 x i32]* %v0, i32 0, i32 0
            %v6 = getelementptr inbounds i32, i32* %v5, i32 1
             */
            getElemPtr(ptr, size, realName, index);
            irBuilder.append(table).append(result).append(" = load i32, i32* ").append(ptr).append("\n");
            return result;
        }
    }

    private boolean isFuncRParams;
    // UnaryExp → Ident '(' [FuncRParams] ')'
    // FuncRParams → Exp { ',' Exp }
    private String generateFunctionCall(Node unaryExp) {
        // Function call: Ident '(' [FuncRParams] ')'
        String funcName = unaryExp.getDefName();
        NewFuncDef tt = getRealFunc(funcName);
        String realName = tt.name;
        String returnType = tt.type == 0 ? "void" : "i32";
        Node funcRParams = unaryExp.getSon("FuncRParams");
        List<String> paramTypes = tt.paramTypes;

        this.isFuncRParams = true;
        List<String> args = new ArrayList<>();
        if (funcRParams != null) {
            for (Node child : funcRParams.getSons()) {
                if (child.isType("Exp")) {
                    args.add(generateExp(child));
                }
            }
        }
        this.isFuncRParams = false;

        irBuilder.append(table);
        String result = null;
        if (!returnType.equals("void")) {
            result = newTemp();
            irBuilder.append(result).append(" = ");
        }
        irBuilder.append("call ").append(returnType).append(" @").append(realName).append("(");

        for (int i = 0; i < args.size(); i++) {
            if (i > 0) irBuilder.append(", ");
            if (i < paramTypes.size()) {
                String paramType = paramTypes.get(i);
                if (paramType.equals("IntArray")) irBuilder.append("i32* ");
                else irBuilder.append("i32 ");
            } else {
                irBuilder.append("i32 ");
            }
            irBuilder.append(args.get(i));
        }
        irBuilder.append(")\n");
        return returnType.equals("void") ? "0" : result;
    }

    // 'if' '(' Cond ')' Stmt [ 'else' Stmt ]
    private void generateIfStmt(Node stmt) {
        String thenLabel = newLabel();
        String elseLabel = newLabel();
        String endLabel = newLabel();
        Node cond = null;
        Node thenStmt = null;
        Node elseStmt = null;

        for (Node child : stmt.getSons()) {
            if (child.isType("Cond")) cond = child;
            else if (child.isType("Stmt")) {
                if (thenStmt == null) thenStmt = child;
                else elseStmt = child;
            }
        }
        if (cond == null) return;

        generateCond(cond, thenLabel, elseStmt != null ? elseLabel : endLabel);

        // then block
        gotoLabel(thenLabel);
        addLabel(thenLabel);
        generateStmt(thenStmt);
        gotoLabel(endLabel);
        // else block
        if (elseStmt != null) {
            addLabel(elseLabel);
            generateStmt(elseStmt);
            gotoLabel(endLabel);
        }
        // end block
        irBuilder.append(endLabel).append(":\n");
    }

    private void generateCond(Node cond, String trueL, String falseL) {
        // Cond → LOrExp
        generateLOrExp(cond.getSon("LOrExp"), trueL, falseL);
    }

    private void addLabel(String label) {
        irBuilder.append(label).append(":\n");
    }

    // TODO:短路求值
    private void generateLOrExp(Node lOrExp, String trueL,
                                  String falseL) {
        // LOrExp → LAndExp | LOrExp '||' LAndExp
        if (lOrExp.getSons().size() == 1) {
            generateLAndExp(lOrExp.getSon("LAndExp"), trueL, falseL);
        }
        else {
            String rightLabel = newLabel();
            generateLOrExp(lOrExp.getSon("LOrExp"), trueL, rightLabel);
            //  if left is ok, goto trueL
            addLabel(rightLabel);
            generateLAndExp(lOrExp.getSon("LAndExp"), trueL, falseL);
        }
    }


    private void generateLAndExp(Node lAndExp, String trueL, String falseL) {
        // LAndExp → EqExp | LAndExp '&&' EqExp
        if (lAndExp.getSons().size() == 1) {
            /*
                %v37 = icmp ne i32 %v36, 0
	            br i1 %v37, label %b_2, label %b_4
	        */
            String result = generateEqExp(lAndExp.getSon("EqExp"));
            irBuilder.append(table + "br i1 ").append(result)
                    .append(", label %").append(trueL)
                    .append(", label %").append(falseL).append("\n");;
        } else {
            String rightLabel = newLabel();
            generateLAndExp(lAndExp.getSon("LAndExp"), rightLabel, falseL);
            // Generate: result = left != 0 && right != 0
            addLabel(rightLabel);
            String result = generateEqExp(lAndExp.getSon("EqExp"));
            irBuilder.append(table + "br i1 ").append(result)
                    .append(", label %").append(trueL)
                    .append(", label %").append(falseL).append("\n");;
        }
    }

    private String generateEqExp(Node eqExp) {
        // EqExp → RelExp | EqExp ('==' | '!=') RelExp
        if (eqExp.getSons().size() == 1) {
            return generateRelExp(eqExp.getSon("RelExp"));
        } else {
            String left = generateEqExp(eqExp.getSon("EqExp"));
            String right = generateRelExp(eqExp.getSon("RelExp"));
            String op = eqExp.getSons().get(1).getToken().getType();
            String result = newTemp();

            if (op.equals("EQL")) {
                irBuilder.append(table).append(result).append(" = icmp eq i32 ").append(left).append(", ").append(right).append("\n");
            } else {
                irBuilder.append(table).append(result).append(" = icmp ne i32 ").append(left).append(", ").append(right).append("\n");
            }

            return result;
        }
    }

    private String generateRelExp(Node relExp) {
        // RelExp → AddExp | RelExp ('<' | '>' | '<=' | '>=') AddExp
        if (relExp.getSons().size() == 1) {
            return generateAddExp(relExp.getSon("AddExp"));
        } else {
            String left = generateRelExp(relExp.getSon("RelExp"));
            String right = generateAddExp(relExp.getSon("AddExp"));
            String op = relExp.getSons().get(1).getToken().getType();
            String result = newTemp();

            if (op.equals("LSS")) {
                irBuilder.append(table).append(result).append(" = icmp slt i32 ").append(left).append(", ").append(right).append("\n");
            } else if (op.equals("GRE")) {
                irBuilder.append(table).append(result).append(" = icmp sgt i32 ").append(left).append(", ").append(right).append("\n");
            } else if (op.equals("LEQ")) {
                irBuilder.append(table).append(result).append(" = icmp sle i32 ").append(left).append(", ").append(right).append("\n");
            } else {
                irBuilder.append(table).append(result).append(" = icmp sge i32 ").append(left).append(", ").append(right).append("\n");
            }
            return result;
        }
    }

    private void gotoLabel(String label) {
        irBuilder.append(table + "br label %").append(label).append("\n");
    }

    // 'for' '(' [ForStmt] ';' [Cond] ';' [ForStmt] ')' Stmt
    // ForStmt → LVal '=' Exp { ',' LVal '=' Exp }
    private void generateFor(Node stmt) {
        String headerLabel = newLabel();
        String bodyLabel = newLabel();
        String continueLabel = newLabel();
        String breakLabel = newLabel();
        String exitLabel = breakLabel;

        breakLabels.push(exitLabel);
        continueLabels.push(continueLabel);

        Node initStmt = null;
        Node cond = null;
        Node updateStmt = null;
        Node bodyStmt = null;
        int seCount = 0;

        for (Node child : stmt.getSons()) {
            if (child.isType("ForStmt")) {
                if (seCount == 0) initStmt = child;
                else updateStmt = child;
            } else if (child.isType("Cond")) {
                cond = child;
            } else if (child.isType("Stmt")) {
                bodyStmt = child;
            }
            if (child.isType("SEMICN")) ++seCount;
        }

        if (initStmt != null) generateForStmtInit(initStmt);

        gotoLabel(headerLabel);
        addLabel(headerLabel);
        String condValue = "1";
        if (cond != null) generateCond(cond, bodyLabel, exitLabel);
        else gotoLabel(bodyLabel);

        irBuilder.append(bodyLabel).append(":\n");
//        blockTerminated = false;
        if (bodyStmt != null) generateStmt(bodyStmt);
//        if (!blockTerminated) {
//            irBuilder.append(table+"br label %").append(continueLabel).append("\n");
//        }
//        blockTerminated = false;
        gotoLabel(continueLabel);

        irBuilder.append(continueLabel).append(":\n");
        if (updateStmt != null) generateForStmtInit(updateStmt);
        irBuilder.append(table+"br label %").append(headerLabel).append("\n");

        irBuilder.append(exitLabel).append(":\n");
//        blockTerminated = false;

        breakLabels.pop();
        continueLabels.pop();
    }

    private void generateForStmtInit(Node forStmt) {
        // ForStmt → LVal '=' Exp { ',' LVal '=' Exp }
        Node node = new Node(233, "fake node");
        for (Node x : forStmt.getSons()) {
            if (x.isType("LVal")) {
                node.add(x);
            } else if (x.isType("Exp")) {
                node.add(x);
                generateAssignStmt(node);
                node = new Node(233, "fake node");
            }
        }
    }

    private String curFuncType = "i32";
    private void generateReturnStmt(Node stmt) {
        this.hasReturn = true;
        Node exp = stmt.getSon("Exp");

        String returnType = curFuncType;

        if (exp != null) {
            String value = generateExp(exp);
            if (returnType.equals("void")) {
                irBuilder.append(table + "ret void\n");
            } else {
                irBuilder.append(table + "ret i32 ").append(value).append("\n");
            }
        } else {
            if (returnType.equals("void")) {
                irBuilder.append(table + "ret void\n");
            } else {
                irBuilder.append(table + "ret i32 0\n");
            }
        }
    }

    //  'printf''('StringConst {','Exp}')'';'
    private void generatePrintfStmt(Node stmt) {
        // Parse printf statement to get format string and arguments
        String formatStr = null;
        List<Node> exps = new ArrayList<>();

        for (Node child : stmt.getSons()) {
            if (child.isType("STRCON")) {
                formatStr = child.getToken().getValue();
            } else if (child.isType("Exp")) {
                exps.add(child);
            }
        }

        formatStr = formatStr.substring(1, formatStr.length() - 1);

        List<String> prints = new ArrayList<>();
        if (formatStr != null) {
            int len = formatStr.length();
            StringBuilder nowStr = new StringBuilder();
            for (int i = 0, j = 0; i < len; ++i) {
                if (formatStr.charAt(i) == '%' &&
                    i + 1 < len && formatStr.charAt(i + 1) == 'd') {
                    if (nowStr.length() > 0) {
                        String sptr = newConstString(nowStr.toString());
                        prints.add(printStr(sptr, curStringLength));
                        nowStr = new StringBuilder();
                    }
                    ++i;
                    String intPtr = generateExp(exps.get(j));
                    ++j;
                    prints.add(printInt(intPtr));
                } else {
                    nowStr.append(formatStr.charAt(i));
                }
            }
            if (nowStr.length() > 0) {
                String sptr = newConstString(nowStr.toString());
                prints.add(printStr(sptr, curStringLength));
            }
        }
        for (String p : prints) irBuilder.append(p);
    }

    private int curStringLength = 0;
    private String newConstString(String value) {
        // add to list for insert to the head
        String name = "@s" + (stringLiteralCounter++);
        addConstString (name, value);
        return name;
    }
    private void addConstString(String name, String init) {
        // \n-> \0
        StringBuilder value = new StringBuilder();
        int cc = 0;
        for (int i = 0; i < init.length(); ++i) {
            ++cc;
            if (init.charAt(i) == '\\' && i + 1 < init.length()) {
                value.append('\\');
                switch(init.charAt(i + 1)) {
                    case 'n': { value.append("0A"); ++i; break; }
                    case 't': { value.append("09"); ++i; break; }
                    case '\"': { value.append("22"); ++i; break; }
                    case '\\': { value.append("5C"); ++i; break; }
                    case 'r': { value.append("0D"); ++i; break; }
                    case 'b': { value.append("08"); ++i; break; }
                    case 'f': { value.append("0C"); ++i; break; }
                    case 'v': { value.append("0B"); ++i; break; }
                    case '0': { value.append("00"); ++i; break; }
                }
            } else {
                value.append(init.charAt(i));
            }
        }
        value.append("\\" + "00"); ++cc;
        curStringLength = cc;
        constStrings.add(new ConstString(name, value.toString(), cc));
    }

    private String printStr(String ptr, int length) {
        StringBuilder sb = new StringBuilder();
        sb.append(table + "call void @putstr(i8* getelementptr inbounds ([")
                .append(length).append(" x i8], [").append(length)
                .append(" x i8]* ").append(ptr).append(", i32 0, i32 0))\n");
        return sb.toString();
    }

    private String printInt(String ptr) {
        StringBuilder sb = new StringBuilder();
        sb.append(table + "call void @putint(i32 ")
                .append(ptr).append(")\n");
        return sb.toString();
    }

    private String newLabel() {
        return "L" + (labelCounter++);
    }

    private String getLabel(String type) {
        return type + "_" + (labelCounter - 1);
    }

    public void output() throws IOException {
        PrintWriter writer = new PrintWriter(new File("llvm_ir.txt"));
        writer.print(irBuilder.toString());
        writer.close();
    }
}
