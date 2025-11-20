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
//======================================

Value Var::eval(Assoc &e) { // evaluation of variable  //part of TODO!!!

    // TODO: TO identify the invalid variable

    // We request all valid variable just need to be a symbol,you should promise:
    //The first character of a variable name cannot be a digit or any character from the set: {.@}
    //If a string can be recognized as a number, it will be prioritized as a number. For example: 1, -1, +123, .123, +124., 1e-3
    //Variable names can overlap with primitives and reserve_words
    //Variable names can contain any non-whitespace characters except #, ', ", `, but the first character cannot be a digit
    //When a variable is not defined in the current scope, your interpreter should output RuntimeError
    
    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
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
                    {E_DISPLAY,  {new Display(new Var("parm")), {"parm"}}},
                    {E_PLUS,     {new PlusVar({}),  {}}},
                    {E_MINUS,    {new MinusVar({}), {}}},
                    {E_MUL,      {new MultVar({}),  {}}},
                    {E_DIV,      {new DivVar({}),   {}}},
                    {E_MODULO,   {new Modulo(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EXPT,     {new Expt(new Var("parm1"), new Var("parm2")), {"parm1","parm2"}}},
                    {E_EQQ,      {new EqualVar({}), {}}},
            };

            auto it = primitive_map.find(primitives[x]);
            //TOD0:to PASS THE parameters correctly;
            //COMPLETE THE CODE WITH THE HINT IN IF SENTENCE WITH CORRECT RETURN VALUE
            if (it != primitive_map.end()) {

                //TODO
                return ProcedureV(it->second.second, it->second.first, e);

            }
            // 变量未定义，抛出运行时错误
            throw RuntimeError("Undefined variable: " + x);  //do we need this??
      }
    }
    return matched_value;
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
int compareNumericValues(const Value &v1, const Value &v2) {
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
}

Value Car::evalRator(const Value &rand) { // car
    //TODO: To complete the car logic
}

Value Cdr::evalRator(const Value &rand) { // cdr
    //TODO: To complete the cdr logic
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    //TODO: To complete the set-car! logic
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
   //TODO: To complete the set-cdr! logic
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
}

Value Quote::eval(Assoc& e) {
    //TODO: To complete the quote logic
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation
    //TODO: To complete the and logic
}

Value OrVar::eval(Assoc &e) { // or with short-circuit evaluation
    //TODO: To complete the or logic
}

Value Not::evalRator(const Value &rand) { // not
    //TODO: To complete the not logic
}

Value If::eval(Assoc &e) {
    //TODO: To complete the if logic
}

Value Cond::eval(Assoc &env) {
    //TODO: To complete the cond logic
}

Value Lambda::eval(Assoc &env) { 
    //TODO: To complete the lambda logic
}

Value Apply::eval(Assoc &e) {
    if (rator->eval(e)->v_type != V_PROC) {throw RuntimeError("Attempt to apply a non-procedure");}

    //TODO: TO COMPLETE THE CLOSURE LOGIC
    Procedure* clos_ptr = ;
    
    //TODO: TO COMPLETE THE ARGUMENT PARSER LOGIC
    std::vector<Value> args;
    if (auto varNode = dynamic_cast<Variadic*>(clos_ptr->e.get())) {
        //TODO
    }
    if (args.size() != clos_ptr->parameters.size()) throw RuntimeError("Wrong number of arguments");
    
    //TODO: TO COMPLETE THE PARAMETERS' ENVIRONMENT LOGIC
    Assoc param_env = ;

    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    //TODO: To complete the define logic
}

Value Let::eval(Assoc &env) {
    //TODO: To complete the let logic
}

Value Letrec::eval(Assoc &env) {
    //TODO: To complete the letrec logic
}

Value Set::eval(Assoc &env) {
    //TODO: To complete the set logic
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
