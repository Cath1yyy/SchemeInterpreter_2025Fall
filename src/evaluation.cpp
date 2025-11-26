/**
 * @file evaluation.cpp
 * @brief Expression evaluation implementation for the Scheme interpreter
 * @author luke36
 * 
 * This file implements evaluation methods for all expression types in the Scheme
 * interpreter. Functions are organized according to ExprType enumeration order
 * from Def.hpp for consistency and maintainability.
 */

#include "value.hpp"
#include "expr.hpp" 
#include "RE.hpp"
#include "syntax.hpp"
#include <cstring>
#include <vector>
#include <map>
#include <climits>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;
static Value convertSyntaxToValue(const Syntax &syntax);//辅助函数
int compareNumericValues(const Value &v1, const Value &v2);
static Value convertSyntaxToValue(const Syntax &syntax);
static Value convertSyntaxListToValue(List* lst);

Value Fixnum::eval(Assoc &e) { // evaluation of a fixnum
    return IntegerV(n);
}

Value RationalNum::eval(Assoc &e) { // evaluation of a rational number
    return RationalV(numerator, denominator);
}

Value StringExpr::eval(Assoc &e) { // evaluation of a string
    return StringV(s);
}

Value True::eval(Assoc &e) { // evaluation of #t
    return BooleanV(true);
}

Value False::eval(Assoc &e) { // evaluation of #f
    return BooleanV(false);
}

Value MakeVoid::eval(Assoc &e) { // (void)
    return VoidV();
}

Value Exit::eval(Assoc &e) { // (exit)
    return TerminateV();
}

Value Unary::eval(Assoc &e) { // evaluation of single-operator primitive
    return evalRator(rand->eval(e));
}

Value Binary::eval(Assoc &e) { // evaluation of two-operators primitive
    return evalRator(rand1->eval(e), rand2->eval(e));
}

Value Variadic::eval(Assoc &e) { // evaluation of multi-operator primitive

    // TODO: TO COMPLETE THE VARIADIC CLASS
    std::vector<Value> args;
    // 对每个参数表达式进行求值
    for (auto &expr : rands) {
        args.push_back(expr->eval(e));
    }
    // 调用具体的操作符求值函数
    return evalRator(args);

}

// 辅助函数定义
// =================================
// 加法辅助函数
static Value addValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 + n2);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int new_num = r1->numerator + n2 * r1->denominator;
        return RationalV(new_num, r1->denominator);
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int new_num = n1 * r2->denominator + r2->numerator;
        return RationalV(new_num, r2->denominator);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int new_num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int new_den = r1->denominator * r2->denominator;
        return RationalV(new_num, new_den);
    }
    throw(RuntimeError("Wrong typename in addition"));
}

// 减法辅助函数
static Value subtractValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 - n2);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int new_num = r1->numerator - n2 * r1->denominator;
        return RationalV(new_num, r1->denominator);
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int new_num = n1 * r2->denominator - r2->numerator;
        return RationalV(new_num, r2->denominator);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int new_num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int new_den = r1->denominator * r2->denominator;
        return RationalV(new_num, new_den);
    }
    throw(RuntimeError("Wrong typename in subtraction"));
}

// 乘法辅助函数
static Value multiplyValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return IntegerV(n1 * n2);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return RationalV(r1->numerator * n2, r1->denominator);
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        return RationalV(n1 * r2->numerator, r2->denominator);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        return RationalV(r1->numerator * r2->numerator, r1->denominator * r2->denominator);
    }
    throw(RuntimeError("Wrong typename in multiplication"));
}

// 除法辅助函数
static Value divideValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        return RationalV(n1, n2);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        return RationalV(r1->numerator, r1->denominator * n2);
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        return RationalV(n1 * r2->denominator, r2->numerator);
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        return RationalV(r1->numerator * r2->denominator, r1->denominator * r2->numerator);
    }
    throw(RuntimeError("Wrong typename in division"));
}

// Cons辅助函数
static Value consValues(const Value &v1, const Value &v2) {
    return PairV(v1, v2);
}

// 比较辅助函数 - 小于
static Value lessThanValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) < 0);
}

// 比较辅助函数 - 小于等于
static Value lessEqualValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) <= 0);
}

// 比较辅助函数 - 等于
static Value equalValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) == 0);
}

// 比较辅助函数 - 大于等于
static Value greaterEqualValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) >= 0);
}

// 比较辅助函数 - 大于
static Value greaterThanValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) > 0);
}

// syntax类转换为Value的辅助函数
static Value convertSyntaxToValue(const Syntax &syntax) {
    SyntaxBase* base = syntax.get();
    
    // 处理数字
    if (Number* num = dynamic_cast<Number*>(base)) {
        return IntegerV(num->n);
    }
    // 处理有理数
    else if (RationalSyntax* rat = dynamic_cast<RationalSyntax*>(base)) {
        return RationalV(rat->numerator, rat->denominator);
    }
    // 处理#t
    else if (dynamic_cast<TrueSyntax*>(base)) {
        return BooleanV(true);
    }
    // 处理#f
    else if (dynamic_cast<FalseSyntax*>(base)) {
        return BooleanV(false);
    }
    // 处理符号
    else if (SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(base)) {
        return SymbolV(sym->s);
    }
    // 处理字符串
    else if (StringSyntax* str = dynamic_cast<StringSyntax*>(base)) {
        return StringV(str->s);
    }
    // 处理列表 - 需要递归处理
    else if (List* lst = dynamic_cast<List*>(base)) {
        return convertSyntaxListToValue(lst);
    }
    else {
        throw RuntimeError("Unknown syntax type in quote");
    }
}

// 辅助函数：将语法列表转换为Value列表
static Value convertSyntaxListToValue(List* lst) {
    if (lst->stxs.empty()) {
        return NullV();  // 空列表
    }
    
    // 递归构建列表
    Value result = NullV();
    for (int i = lst->stxs.size() - 1; i >= 0; i--) {
        Value element_value = convertSyntaxToValue(lst->stxs[i]);
        result = PairV(element_value, result);
    }
    return result;
}
//======================================

Value Var::eval(Assoc &e) { // evaluation of variable  //debug later!!!
    if (primitives.count(x)) {
            static std::map<ExprType, std::pair<Expr, std::vector<std::string>>> primitive_map = {
                    {E_VOID,     {new MakeVoid(), {}}},
                    {E_EXIT,     {new Exit(), {}}},
                    {E_BOOLQ,    {new IsBoolean(new Var("parm")), {"parm"}}},
                    {E_INTQ,     {new IsFixnum(new Var("parm")), {"parm"}}},
                    {E_NULLQ,    {new IsNull(new Var("parm")), {"parm"}}},
                    {E_PAIRQ,    {new IsPair(new Var("parm")), {"parm"}}},
                    {E_PROCQ,    {new IsProcedure(new Var("parm")), {"parm"}}},
                    {E_SYMBOLQ,  {new IsSymbol(new Var("parm")), {"parm"}}},
                    {E_STRINGQ,  {new IsString(new Var("parm")), {"parm"}}},
                    {E_LISTQ,    {new IsList(new Var("parm")), {"parm"}}},
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new IsEq(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_LT,       {new LessVar({}), {}}},
                    {E_LE,       {new LessEqVar({}), {}}},
                    {E_EQ,       {new EqualVar({}), {}}},
                    {E_GE,       {new GreaterEqVar({}), {}}},
                    {E_GT,       {new GreaterVar({}), {}}},
                    {E_CONS,     {new Cons(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_CAR,      {new Car(new Var("parm")), {"parm"}}},
                    {E_CDR,      {new Cdr(new Var("parm")), {"parm"}}},
                    {E_LIST,     {new ListFunc({}), {}}},
                    {E_SETCAR,   {new SetCar(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_SETCDR,   {new SetCdr(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_NOT,      {new Not(new Var("parm")), {"parm"}}},
                    {E_AND,      {new AndVar({}), {}}},
                    {E_OR,       {new OrVar({}), {}}}
            };
            auto it = primitive_map.find(primitives[x]);
            //TOD0:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != primitive_map.end()) {

                //TODO
                return ProcedureV(it->second.second, it->second.first, e);

            }
    }

    // TODO: TO identify the invalid variable
    if (!e.get()) {
        std::cerr << "ERROR: Null environment in Var::eval for variable: " << x << std::endl;
        throw RuntimeError("Null environment");
    }
    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    
    Value matched_value = find(x, e);

    //===================================
    std::cerr << "DEBUG: Looking up '" << x << "' in environment, result: " 
          << (matched_value.get() != nullptr ? "FOUND" : "NOT FOUND") << std::endl;
    //===================================

    if (matched_value.get() != nullptr) {
        return matched_value;
    }
    // 变量未定义，抛出运行时错误
    throw RuntimeError("Undefined variable: " + x);  //do we need this??
    
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +  //check later

    //TODO: To complete the addition logic
    /*
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 + n2);
    }
    // 有理数 + 整数
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int new_num = r1->numerator + n2 * r1->denominator;
        return RationalV(new_num, r1->denominator);
    }
    // 整数 + 有理数
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int new_num = n1 * r2->denominator + r2->numerator;
        return RationalV(new_num, r2->denominator);
    }
    // 有理数 + 有理数
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int new_num = r1->numerator * r2->denominator + r2->numerator * r1->denominator;
        int new_den = r1->denominator * r2->denominator;
        return RationalV(new_num, new_den);
    }*/
    
    //throw(RuntimeError("Wrong typename"));
    return addValues(rand1, rand2);
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -  //check later

    //TODO: To complete the substraction logic
    /*
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 - n2);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        int new_num = r1->numerator - n2 * r1->denominator;
        return RationalV(new_num, r1->denominator);
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int new_num = n1 * r2->denominator - r2->numerator;
        return RationalV(new_num, r2->denominator);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        int new_num = r1->numerator * r2->denominator - r2->numerator * r1->denominator;
        int new_den = r1->denominator * r2->denominator;
        return RationalV(new_num, new_den);
    }
    
    throw(RuntimeError("Wrong typename"));*/
    return subtractValues(rand1, rand2);
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *  //check later

    //TODO: To complete the Multiplication logic
    /*if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return IntegerV(n1 * n2);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        return RationalV(r1->numerator * n2, r1->denominator);
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return RationalV(n1 * r2->numerator, r2->denominator);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        return RationalV(r1->numerator * r2->numerator, r1->denominator * r2->denominator);
    }

    throw(RuntimeError("Wrong typename"));*/
    return multiplyValues(rand1, rand2);
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /  //check later

    //TODO: To complete the division logic
    /*if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        return RationalV(n1, n2);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        int n2 = dynamic_cast<Integer*>(rand2.get())->n;
        if (n2 == 0) throw RuntimeError("Division by zero");
        return RationalV(r1->numerator, r1->denominator * n2);
    }
    else if (rand1->v_type == V_INT && rand2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(rand1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        return RationalV(n1 * r2->denominator, r2->numerator);
    }
    else if (rand1->v_type == V_RATIONAL && rand2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(rand1.get());
        Rational* r2 = dynamic_cast<Rational*>(rand2.get());
        if (r2->numerator == 0) throw RuntimeError("Division by zero");
        return RationalV(r1->numerator * r2->denominator, r1->denominator * r2->numerator);
    }

    throw(RuntimeError("Wrong typename"));*/
    return divideValues(rand1, rand2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int dividend = dynamic_cast<Integer*>(rand1.get())->n;
        int divisor = dynamic_cast<Integer*>(rand2.get())->n;
        if (divisor == 0) {
            throw(RuntimeError("Division by zero"));
        }
        return IntegerV(dividend % divisor);
    }
    throw(RuntimeError("modulo is only defined for integers"));
}

Value PlusVar::evalRator(const std::vector<Value> &args) { // + with multiple args

    // Complete the addition logic by folding over the arguments using a Plus instance
    if (args.empty()) return IntegerV(0);
    
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {

        /*// 创建临时的Plus表达式对象来调用evalRator
        Plus plus_expr(Expr(new Fixnum(0)), Expr(new Fixnum(0))); // 参数是dummy，不会实际使用
        result = plus_expr.evalRator(result, args[i]);*/
        result = addValues(result, args[i]);

    }
    return result;
    
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args

    //TODO: To complete the substraction logic
    if (args.empty()) throw RuntimeError("- requires at least one argument");
    if (args.size() == 1) {
        return subtractValues(IntegerV(0), args[0]); // 单参数：0 - x
    }
    
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = subtractValues(result, args[i]);
    }
    return result;

}

Value MultVar::evalRator(const std::vector<Value> &args) { // * with multiple args

    //TODO: To complete the multiplication logic
    if (args.empty()) return IntegerV(1);
    
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = multiplyValues(result, args[i]);
    }
    return result;

}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args

    //TODO: To complete the divisor logic
    if (args.empty()) throw RuntimeError("/ requires at least one argument");
    if (args.size() == 1) {
        return divideValues(IntegerV(1), args[0]); // 单参数：1 / x
    }
    
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = divideValues(result, args[i]);
    }
    return result;

}

Value Expt::evalRator(const Value &rand1, const Value &rand2) { // expt
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                if (result > INT_MAX || result < INT_MIN) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            b *= b;
            if (b > INT_MAX || b < INT_MIN) {
                if (exp > 1) {
                    throw(RuntimeError("Integer overflow in expt"));
                }
            }
            exp /= 2;
        }
        
        return IntegerV((int)result);
    }
    throw(RuntimeError("Wrong typename"));
}

//A FUNCTION TO SIMPLIFY THE COMPARISON WITH INTEGER AND RATIONAL NUMBER
/*int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        int n2 = dynamic_cast<Integer*>(v2.get())->n;
        int left = r1->numerator;
        int right = n2 * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        int n1 = dynamic_cast<Integer*>(v1.get())->n;
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = n1 * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}*/
int compareNumericValues(const Value &v1, const Value &v2) {
    if (v1->v_type == V_INT && v2->v_type == V_INT) {
        Integer* i1 = dynamic_cast<Integer*>(v1.get());
        Integer* i2 = dynamic_cast<Integer*>(v2.get());
        // 添加null检查
        if (!i1 || !i2) throw RuntimeError("Type conversion failed in integer comparison");
        int n1 = i1->n;
        int n2 = i2->n;
        return (n1 < n2) ? -1 : (n1 > n2) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_INT) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Integer* i2 = dynamic_cast<Integer*>(v2.get());
        // 添加null检查
        if (!r1 || !i2) throw RuntimeError("Type conversion failed in rational-integer comparison");
        int left = r1->numerator;
        int right = i2->n * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        Integer* i1 = dynamic_cast<Integer*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        // 添加null检查
        if (!i1 || !r2) throw RuntimeError("Type conversion failed in integer-rational comparison");
        int left = i1->n * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());
        // 添加null检查
        if (!r1 || !r2) throw RuntimeError("Type conversion failed in rational comparison");
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    //TODO: To complete the less logic
    return lessThanValues(rand1, rand2);
    //throw(RuntimeError("Wrong typename"));
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    //TODO: To complete the lesseq logic
    return lessEqualValues(rand1, rand2);
    //throw(RuntimeError("Wrong typename"));
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    //TODO: To complete the equal logic
    return equalValues(rand1, rand2);
    throw(RuntimeError("Wrong typename"));
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    //TODO: To complete the greatereq logic
    return greaterEqualValues(rand1, rand2);
    throw(RuntimeError("Wrong typename"));
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    //TODO: To complete the greater logic
    return greaterThanValues(rand1, rand2);
    throw(RuntimeError("Wrong typename"));
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args

    //TODO: To complete the less logic
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);

}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args

    //TODO: To complete the lesseq logic
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);

}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args

    //TODO: To complete the equal logic
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);

}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args

    //TODO: To complete the greatereq logic
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);

}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args

    //TODO: To complete the greater logic
    if (args.size() < 2) return BooleanV(true);
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);

}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons

    //TODO: To complete the cons logic
    return consValues(rand1, rand2);

}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function

    //TODO: To complete the list logic
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; i--) {
        result = consValues(args[i], result);
    }
    return result;

}

Value IsList::evalRator(const Value &rand) { // list?

    //TODO: To complete the list? logic
    Value current = rand;
    // 遍历cdr链，直到遇到非Pair
    while (current->v_type == V_PAIR) {
        Pair* p = dynamic_cast<Pair*>(current.get());
        current = p->cdr;
    }
    // 列表必须以空列表结尾
    return BooleanV(current->v_type == V_NULL);

}

Value Car::evalRator(const Value &rand) { // car

    //TODO: To complete the car logic
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("Car requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->car;

}

Value Cdr::evalRator(const Value &rand) { // cdr

    //TODO: To complete the cdr logic
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("Cdr requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->cdr;

}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!

    //TODO: To complete the set-car! logic
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("Set-car! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->car = rand2;  // 直接修改car指针
    return VoidV();   // 返回void值

}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!

   //TODO: To complete the set-cdr! logic
   if (rand1->v_type != V_PAIR) {
        throw RuntimeError("Set-cdr! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->cdr = rand2;  // 直接修改cdr指针
    return VoidV();   // 返回void值

}

Value IsEq::evalRator(const Value &rand1, const Value &rand2) { // eq?
    // 检查类型是否为 Integer
    if (rand1->v_type == V_INT && rand2->v_type == V_INT) {
        return BooleanV((dynamic_cast<Integer*>(rand1.get())->n) == (dynamic_cast<Integer*>(rand2.get())->n));
    }
    // 检查类型是否为 Boolean
    else if (rand1->v_type == V_BOOL && rand2->v_type == V_BOOL) {
        return BooleanV((dynamic_cast<Boolean*>(rand1.get())->b) == (dynamic_cast<Boolean*>(rand2.get())->b));
    }
    // 检查类型是否为 Symbol
    else if (rand1->v_type == V_SYM && rand2->v_type == V_SYM) {
        return BooleanV((dynamic_cast<Symbol*>(rand1.get())->s) == (dynamic_cast<Symbol*>(rand2.get())->s));
    }
    // 检查类型是否为 Null 或 Void
    else if ((rand1->v_type == V_NULL && rand2->v_type == V_NULL) ||
             (rand1->v_type == V_VOID && rand2->v_type == V_VOID)) {
        return BooleanV(true);
    } else {
        return BooleanV(rand1.get() == rand2.get());
    }
}

Value IsBoolean::evalRator(const Value &rand) { // boolean?
    return BooleanV(rand->v_type == V_BOOL);
}

Value IsFixnum::evalRator(const Value &rand) { // number?
    return BooleanV(rand->v_type == V_INT);
}

Value IsNull::evalRator(const Value &rand) { // null?
    return BooleanV(rand->v_type == V_NULL);
}

Value IsPair::evalRator(const Value &rand) { // pair?
    return BooleanV(rand->v_type == V_PAIR);
}

Value IsProcedure::evalRator(const Value &rand) { // procedure?
    return BooleanV(rand->v_type == V_PROC);
}

Value IsSymbol::evalRator(const Value &rand) { // symbol?
    return BooleanV(rand->v_type == V_SYM);
}

Value IsString::evalRator(const Value &rand) { // string?
    return BooleanV(rand->v_type == V_STRING);
}

Value Begin::eval(Assoc &e) {

    //TODO: To complete the begin logic
    if (es.empty()) {
        return VoidV();  // 空begin返回void
    }
    
    // 初始化result为第一个表达式的值
    Value result = es[0]->eval(e);
    // 依次执行剩余的表达式，只保留最后一个结果
    for (size_t i = 1; i < es.size(); i++) {
        result = es[i]->eval(e);
    }
    return result;

}

Value Quote::eval(Assoc& e) {
    //TODO: To complete the quote logic
    // 引用表达式直接返回其内容，不进行求值
    // 根据expr.cpp，Quote使用成员变量s（Syntax类型）
    return convertSyntaxToValue(s);

}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    //TODO: To complete the and logic
    if (rands.empty()) return BooleanV(true); // 空and返回#t
    
    for (auto &expr : rands) {
        Value result = expr->eval(e);
        // 如果遇到#f，立即返回#f（短路求值）
        if (result->v_type == V_BOOL && !dynamic_cast<Boolean*>(result.get())->b) {
            return BooleanV(false);
        }
    }
    // 所有表达式都为真，返回最后一个表达式的结果
    return rands.back()->eval(e);
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    //TODO: To complete the or logic
    if (rands.empty()) return BooleanV(false); // 空or返回#f
    
    for (auto &expr : rands) {
        Value result = expr->eval(e);
        // 如果遇到真值，立即返回该值（短路求值）
        if (result->v_type != V_BOOL || dynamic_cast<Boolean*>(result.get())->b) {
            return result;
        }
    }
    // 所有表达式都为假，返回#f
    return BooleanV(false);
}

Value Not::evalRator(const Value &rand) { // not
    //TODO: To complete the not logic
    if (rand->v_type == V_BOOL) {
        return BooleanV(!dynamic_cast<Boolean*>(rand.get())->b);
    }
    // 非布尔值在Scheme中也被视为真值，not返回#f
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    //TODO: To complete the if logic
    Value test_val = cond->eval(e);
    
    // 在Scheme中，只有#f被视为假，其他所有值都为真
    bool test_result = true;
    if (test_val->v_type == V_BOOL) {
        //test_result = dynamic_cast<Boolean*>(test_val.get())->b;
        Boolean* bool_val = dynamic_cast<Boolean*>(test_val.get());
        if (!bool_val) throw RuntimeError("Type conversion failed in if condition");
        test_result = bool_val->b;
    }
    
    if (test_result) {
        return conseq->eval(e);
    } else if (alter.get() != nullptr) {  // 检查alter是否不为空指针
        return alter->eval(e);
    } else {
        // 没有else分支时返回未定义值
        return VoidV();
    }
}

Value Cond::eval(Assoc &env) {

    //TODO: To complete the cond logic
    // 初始化result为void，如果没有匹配分支则返回void
    Value result = VoidV();
    
    for (auto &clause : clauses) {
        if (clause.empty()) continue;
        
        if (clause.size() == 1) {
            // 只有条件没有分支，如 (cond (#t))
            Value test = clause[0]->eval(env);
            if (test->v_type != V_BOOL || dynamic_cast<Boolean*>(test.get())->b) {
                return test;  // 返回条件值本身
            }
        } else {
            // 正常分支：条件 + 多个表达式
            Value test = clause[0]->eval(env);
            if (test->v_type != V_BOOL || dynamic_cast<Boolean*>(test.get())->b) {
                // 执行该分支的所有表达式，返回最后一个的值
                if (clause.size() < 2) {
                    throw RuntimeError("Cond clause with no body expressions");
                }
                result = clause[1]->eval(env);  // 先初始化result
                for (size_t i = 2; i < clause.size(); i++) {
                    result = clause[i]->eval(env);
                }
                return result;
            }
        }
    }
    return result;  // 返回初始化的void值

}

Value Lambda::eval(Assoc &env) { 

    //TODO: To complete the lambda logic
    return ProcedureV(x, e, env);

}

Value Apply::eval(Assoc &e) {  //check later!!1
    Value proc_val = rator->eval(e);
    if (proc_val->v_type != V_PROC) {
        throw RuntimeError("Attempt to apply a non-procedure");
    }
    //if (rator->eval(e)->v_type != V_PROC) {
    //    throw RuntimeError("Attempt to apply a non-procedure");
    //}

    //TODO: TO COMPLETE THE CLOSURE LOGIC
    Procedure* clos_ptr = dynamic_cast<Procedure*>(proc_val.get());
    if (clos_ptr == nullptr) {  //check if nullptr, throw error instead of segmentation fault
        throw RuntimeError("Invalid procedure object");
    }

    // 确保闭包表达式不为空
    if (clos_ptr->e.get() == nullptr) {  //check!!!
        throw RuntimeError("Procedure body is null");
    }

    // 检查参数列表是否有效
    if (clos_ptr->parameters.size() != rand.size()) {
        throw RuntimeError("Wrong number of arguments");
    }
    
    //TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
    // 对所有的实际参数表达式进行求值，得到实参列表
    std::vector<Value> args;
    for (auto &expr : rand) {
        args.push_back(expr->eval(e));
    }
    /*std::vector<Value> args;
    if (auto varNode = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
        //TODO
        throw RuntimeError("Invalid procedure object");
    }*/

    if (args.size() != clos_ptr->parameters.size())
        throw RuntimeError("Wrong number of arguments");
    
    //TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
    // 扩展环境：在闭包的词法环境基础上，将形参与实参绑定
    Assoc param_env = clos_ptr->env;
    for (size_t i = 0; i < clos_ptr->parameters.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    //TODO
    // 定义变量，将标识符绑定到环境中
    /*Value value = e->eval(env);
    env = extend(var, value, env);
    return VoidV();*/
    // 对于函数定义，我们需要支持递归
    // 先创建一个占位符
    env = extend(var, VoidV(), env);
    
    // 计算实际值（在包含占位符的环境中）
    Value value = e->eval(env);
    
    // 更新为实际值
    modify(var, value, env);
    
    return VoidV();
}

Value Let::eval(Assoc &env) {

    //TODO: To complete the let logic
    Assoc new_env = env;
    for (auto &binding : bind) {
        Value val = binding.second->eval(env);
        new_env = extend(binding.first, val, new_env);
    }
    return body->eval(new_env);

}

Value Letrec::eval(Assoc &env) {

    //TODO: To complete the letrec logic
    // 先创建占位符绑定
    Assoc new_env = env;
    for (auto &binding : bind) {
        new_env = extend(binding.first, VoidV(), new_env);
    }
    
    // 然后计算实际值
    for (auto &binding : bind) {
        Value val = binding.second->eval(new_env);
        modify(binding.first, val, new_env);
    }
    
    return body->eval(new_env);

}

Value Set::eval(Assoc &env) {
    //TODO: To complete the set logic
    // 修改变量的值
    Value value = e->eval(env);
    
    // 在环境中查找变量并修改其值
    Assoc current = env;
    while (current.get() != nullptr) {
        if (current->x == var) {
            current->v = value;  // 根据value.cpp，成员变量是v
            return VoidV();
        }
        current = current->next;
    }
    
    // 如果变量未定义，抛出错误
    throw RuntimeError("set!: cannot set variable before definition: " + var);
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        rand->show(std::cout);
    }
    
    return VoidV();
}
