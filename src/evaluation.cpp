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
    std::vector<Value> args;
    for (const auto& r : rands) {
        args.push_back(r->eval(e));
    }
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

// 比较辅助函数：小于
static Value lessThanValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) < 0);
}

// 比较辅助函数：小于等于
static Value lessEqualValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) <= 0);
}

// 比较辅助函数：等于
static Value equalValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) == 0);
}

// 比较辅助函数：大于等于
static Value greaterEqualValues(const Value &v1, const Value &v2) {
    return BooleanV(compareNumericValues(v1, v2) >= 0);
}

// 比较辅助函数：大于
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

Value Var::eval(Assoc &e) { // evaluation of variable
    if ((x.empty()) || (std::isdigit(x[0]) || x[0] == '.' || x[0] == '@')) 
        throw RuntimeError("Wrong variable name");
    for (int i = 0; i < x.size(); i++) {
        if (x[i] == '#') {
            throw(RuntimeError("undefined variable"));
        }
    }

    Value matched_value = find(x, e);
    if (matched_value.get() == nullptr) {
        if (primitives.count(x)) {
            Expr exp = nullptr;
            int type_name = primitives[x];
            switch (type_name) {
                case E_MUL: { exp = (new Mult(new Var("parm1"), new Var("parm2"))); break; }
                case E_MINUS: { exp = (new Minus(new Var("parm1"), new Var("parm2"))); break; }
                case E_PLUS: { exp = (new Plus(new Var("parm1"), new Var("parm2"))); break; }
                case E_DIV: { exp = (new Div(new Var("parm1"), new Var("parm2"))); break; }
                case E_MODULO: { exp = (new Modulo(new Var("parm1"), new Var("parm2"))); break; }
                case E_LT: { exp = (new Less(new Var("parm1"), new Var("parm2"))); break; }
                case E_LE: { exp = (new LessEq(new Var("parm1"), new Var("parm2"))); break; }
                case E_EQ: { exp = (new Equal(new Var("parm1"), new Var("parm2"))); break; }
                case E_GE: { exp = (new GreaterEq(new Var("parm1"), new Var("parm2"))); break; }
                case E_GT: { exp = (new Greater(new Var("parm1"), new Var("parm2"))); break; }
                case E_VOID: { exp = (new MakeVoid()); break; }
                case E_EQQ: { exp = (new IsEq(new Var("parm1"), new Var("parm2"))); break; }
                case E_BOOLQ: { exp = (new IsBoolean(new Var("parm"))); break; }
                case E_INTQ: { exp = (new IsFixnum(new Var("parm"))); break; }
                case E_NULLQ: { exp = (new IsNull(new Var("parm"))); break; }
                case E_PAIRQ: { exp = (new IsPair(new Var("parm"))); break; }
                case E_PROCQ: { exp = (new IsProcedure(new Var("parm"))); break; }
                case E_LISTQ: { exp = (new IsList(new Var("parm"))); break; }
                case E_SYMBOLQ: { exp = (new IsSymbol(new Var("parm"))); break; }
                case E_STRINGQ: { exp = (new IsString(new Var("parm"))); break; }
                case E_CONS: { exp = (new Cons(new Var("parm1"), new Var("parm2"))); break; }
                case E_EXPT: { exp = (new Expt(new Var("parm1"), new Var("parm2"))); break; }
                case E_NOT: { exp = (new Not(new Var("parm"))); break; }
                case E_CAR: { exp = (new Car(new Var("parm"))); break; }
                case E_CDR: { exp = (new Cdr(new Var("parm"))); break; }
                case E_SETCAR: { exp = (new SetCar(new Var("parm1"), new Var("parm2"))); break; }
                case E_SETCDR: { exp = (new SetCdr(new Var("parm1"), new Var("parm2"))); break; }
                case E_DISPLAY: { exp = (new Display(new Var("parm"))); break; }
                case E_EXIT: { exp = (new Exit()); break; }
            }
            std::vector<std::string> parameters_;
            if (dynamic_cast<Binary*>(exp.get())) {
                parameters_.push_back("parm1");
                parameters_.push_back("parm2");
            } else if (dynamic_cast<Unary*>(exp.get())) {
                parameters_.push_back("parm");
            }
            return ProcedureV(parameters_, exp, e);
        } else {
            throw(RuntimeError("undefined variable"));
        }
    }
    return matched_value;
}

Value Plus::evalRator(const Value &rand1, const Value &rand2) { // +
    return addValues(rand1, rand2);
}

Value Minus::evalRator(const Value &rand1, const Value &rand2) { // -
    return subtractValues(rand1, rand2);
}

Value Mult::evalRator(const Value &rand1, const Value &rand2) { // *
    return multiplyValues(rand1, rand2);
}

Value Div::evalRator(const Value &rand1, const Value &rand2) { // /
    return divideValues(rand1, rand2);
}

Value Modulo::evalRator(const Value &rand1, const Value &rand2) { // modulo
    // modulo只对整数有效
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
   if (args.empty()) return IntegerV(0);
    
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = addValues(result, args[i]);

    }
    return result;
}

Value MinusVar::evalRator(const std::vector<Value> &args) { // - with multiple args

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
    
    if (args.empty()) return IntegerV(1);
    
    Value result = args[0];
    for (size_t i = 1; i < args.size(); i++) {
        result = multiplyValues(result, args[i]);
    }
    return result;
}

// GCD 辅助函数（用于有理数化简）
static int gcd_helper(int a, int b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b != 0) {
        int temp = b;
        b = a % b;
        a = temp;
    }
    return a;
}

// 有理数乘法
static Value multiply_rationals(int num1, int den1, int num2, int den2) {
    int new_num = num1 * num2;
    int new_den = den1 * den2;
    int g = gcd_helper(new_num, new_den);
    new_num /= g;
    new_den /= g;
    if (new_den < 0) {
        new_num = -new_num;
        new_den = -new_den;
    }
    return RationalV(new_num, new_den);
}

Value DivVar::evalRator(const std::vector<Value> &args) { // / with multiple args
    
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
    if (rand1->v_type == V_INT and rand2->v_type == V_INT) {
        int base = dynamic_cast<Integer*>(rand1.get())->n;
        int exponent = dynamic_cast<Integer*>(rand2.get())->n;
        
        // 处理特殊情况
        if (exponent < 0) {
            throw(RuntimeError("Negative exponent not supported for integers"));
        }
        if (base == 0 && exponent == 0) {
            throw(RuntimeError("0^0 is undefined"));
        }
        
        // 计算 base^exponent
        long long result = 1;
        long long b = base;
        int exp = exponent;
        
        // 快速幂
        while (exp > 0) {
            if (exp % 2 == 1) {
                result *= b;
                // 检查溢出
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

        if (!r1 || !i2) throw RuntimeError("Type conversion failed in rational-integer comparison");
        int left = r1->numerator;
        int right = i2->n * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_INT && v2->v_type == V_RATIONAL) {
        Integer* i1 = dynamic_cast<Integer*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());

        if (!i1 || !r2) throw RuntimeError("Type conversion failed in integer-rational comparison");
        int left = i1->n * r2->denominator;
        int right = r2->numerator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    else if (v1->v_type == V_RATIONAL && v2->v_type == V_RATIONAL) {
        Rational* r1 = dynamic_cast<Rational*>(v1.get());
        Rational* r2 = dynamic_cast<Rational*>(v2.get());

        if (!r1 || !r2) throw RuntimeError("Type conversion failed in rational comparison");
        int left = r1->numerator * r2->denominator;
        int right = r2->numerator * r1->denominator;
        return (left < right) ? -1 : (left > right) ? 1 : 0;
    }
    throw RuntimeError("Wrong typename in numeric comparison");
}

Value Less::evalRator(const Value &rand1, const Value &rand2) { // <
    return BooleanV(compareNumericValues(rand1, rand2) < 0);
}

Value LessEq::evalRator(const Value &rand1, const Value &rand2) { // <=
    
    return lessEqualValues(rand1, rand2);
}

Value Equal::evalRator(const Value &rand1, const Value &rand2) { // =
    return BooleanV(compareNumericValues(rand1, rand2) == 0);
}

Value GreaterEq::evalRator(const Value &rand1, const Value &rand2) { // >=
    return BooleanV(compareNumericValues(rand1, rand2) >= 0);
}

Value Greater::evalRator(const Value &rand1, const Value &rand2) { // >
    return BooleanV(compareNumericValues(rand1, rand2) > 0);
}

Value LessVar::evalRator(const std::vector<Value> &args) { // < with multiple args
    
    if (args.size() < 2){
        throw(RuntimeError("< requires at least 2 arguments"));
    }
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) >= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value LessEqVar::evalRator(const std::vector<Value> &args) { // <= with multiple args
    
    if (args.size() < 2)
        throw(RuntimeError("<= requires at least 2 arguments"));
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) > 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value EqualVar::evalRator(const std::vector<Value> &args) { // = with multiple args
    
    if (args.size() < 2)
        throw(RuntimeError("= requires at least 2 arguments"));
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) != 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterEqVar::evalRator(const std::vector<Value> &args) { // >= with multiple args
    
    if (args.size() < 2)
        throw(RuntimeError(">= requires at least 2 arguments"));
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) < 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value GreaterVar::evalRator(const std::vector<Value> &args) { // > with multiple args
    
    if (args.size() < 2)
        throw(RuntimeError("> requires at least 2 arguments"));
    for (size_t i = 0; i < args.size() - 1; i++) {
        if (compareNumericValues(args[i], args[i+1]) <= 0) {
            return BooleanV(false);
        }
    }
    return BooleanV(true);
}

Value Cons::evalRator(const Value &rand1, const Value &rand2) { // cons
    return consValues(rand1, rand2);
}

Value ListFunc::evalRator(const std::vector<Value> &args) { // list function

    if (args.empty()) {
        return NullV(); // 空列表
    }
    
    // 从右向左构建列表 (cons 第一个参数 到 (递归构建剩余参数的列表))
    Value result = NullV();
    for (int i = args.size() - 1; i >= 0; i--) {
        result = consValues(args[i], result);
    }
    return result;

}

Value IsList::evalRator(const Value &rand) { // list?
    // 参考 github 上示范代码
    // list? 检查值是否为正常列表（包括空列表）
    // 正常列表是以 null 结尾的 pair 链，或者就是 null
    if (rand->v_type == V_NULL) {
        return BooleanV(true); // 空列表是列表
    }
    
    if (rand->v_type != V_PAIR) {
        return BooleanV(false); // 不是 pair 就不是列表
    }
    
    // 使用快慢指针检测环形列表并找到列表末尾
    Value slow = rand;
    Value fast = rand;
    
    while (true) {
        // 快指针前进两步
        if (fast->v_type != V_PAIR) break;
        fast = dynamic_cast<Pair*>(fast.get())->cdr;
        if (fast->v_type != V_PAIR) break;
        fast = dynamic_cast<Pair*>(fast.get())->cdr;
        
        // 慢指针前进一步
        slow = dynamic_cast<Pair*>(slow.get())->cdr;
        
        // 检测环形
        if (slow.get() == fast.get()) {
            return BooleanV(false); // 不是正常列表
        }
    }
    
    // 检查最后是否以 null 结尾
    return BooleanV(fast->v_type == V_NULL);
}

Value Car::evalRator(const Value &rand) { // car
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("Car requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->car;
}

Value Cdr::evalRator(const Value &rand) { // cdr
    if (rand->v_type != V_PAIR) {
        throw RuntimeError("Cdr requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand.get());
    return p->cdr;
}

Value SetCar::evalRator(const Value &rand1, const Value &rand2) { // set-car!
    if (rand1->v_type != V_PAIR) {
        throw RuntimeError("Set-car! requires a pair");
    }
    Pair* p = dynamic_cast<Pair*>(rand1.get());
    p->car = rand2;  // 直接修改car指针
    return VoidV();   // 返回void值
}

Value SetCdr::evalRator(const Value &rand1, const Value &rand2) { // set-cdr!
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

Value IsFixnum::evalRator(const Value &rand) { // fixnum?
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
    if (es.size() == 0) return VoidV();
    
    // 查找连续的内部定义
    std::vector<std::pair<std::string, Expr>> internal_defs;
    int first_non_define = 0;
    
    for (int i = 0; i < es.size(); i++) {
        if (es[i]->e_type == E_DEFINE) {
            Define* def = dynamic_cast<Define*>(es[i].get());
            if (def) {
                internal_defs.push_back({def->var, def->e});
                first_non_define = i + 1;
            } else {
                break; // 不是连续的定义
            }
        } else {
            break; // 不是连续的定义
        }
    }
    
    // 如果有内部定义，使用类似 letrec 的语义
    if (!internal_defs.empty()) {
        // 创建新环境，先绑定所有变量为 nullptr
        Assoc new_env = e;
        for (const auto &def : internal_defs) {
            new_env = extend(def.first, Value(nullptr), new_env);
        }
        
        // 在新环境中求值所有定义的表达式
        for (const auto &def : internal_defs) {
            Value val = def.second->eval(new_env);
            modify(def.first, val, new_env);
        }
        
        // 在新环境中执行剩余的表达式
        if (first_non_define >= es.size()) {
            return VoidV(); // 只有定义，没有其他表达式
        }
        
        for (int i = first_non_define; i < es.size() - 1; i++) {
            es[i]->eval(new_env);
        }
        return es[es.size() - 1]->eval(new_env);
    }
    
    // 没有内部定义，使用原来的逻辑
    for (int i = 0; i < es.size() - 1; i++) {
        es[i]->eval(e);
    }
    return es[es.size() - 1]->eval(e);
}

Value Quote::eval(Assoc& e) {
    if (dynamic_cast<TrueSyntax*>(s.get())) 
        return BooleanV(true);
    else if (dynamic_cast<FalseSyntax*>(s.get())) 
        return BooleanV(false);
    else if (dynamic_cast<Number*>(s.get()))  // 使用Number而不是Integer
        return IntegerV(dynamic_cast<Number*>(s.get())->n);
    else if (dynamic_cast<SymbolSyntax*>(s.get())) 
        return SymbolV(dynamic_cast<SymbolSyntax*>(s.get())->s);
    else if (dynamic_cast<StringSyntax*>(s.get())) 
        return StringV(dynamic_cast<StringSyntax*>(s.get())->s);
    else if (dynamic_cast<List*>(s.get())) {
        auto stxs_got = dynamic_cast<List*>(s.get())->stxs; 
        List* temp = new List;
        if (dynamic_cast<List*>(s.get())->stxs.empty()) {
            return NullV();
        } else if (stxs_got.size() == 1) {
            return PairV(Value(Quote(stxs_got[0]).eval(e)), NullV());
        } else {
            int pos = -1, cnt = 0, len = stxs_got.size();
            for (int i = 0; i < len; i++) {
                pos = (((dynamic_cast<SymbolSyntax*>(stxs_got[i].get())) && (dynamic_cast<SymbolSyntax*>(stxs_got[i].get())->s == ".")) ? (i) : (pos));
                cnt = (((dynamic_cast<SymbolSyntax*>(stxs_got[i].get())) && (dynamic_cast<SymbolSyntax*>(stxs_got[i].get())->s == ".")) ? (cnt + 1) : (cnt));
            }
            if ((cnt > 1 || ((pos != len - 2) && (cnt))) || (cnt == 1 && (len < 3))) {
                throw RuntimeError("Parm isn't fit");
            }
            if (len == 3) {
                if ((dynamic_cast<SymbolSyntax*>(stxs_got[1].get())) && (dynamic_cast<SymbolSyntax*>(stxs_got[1].get())->s == ".")) {
                    return PairV(Quote(stxs_got[0]).eval(e), Quote(stxs_got[2]).eval(e));
                }
            }
            (*temp).stxs = std::vector<Syntax>(stxs_got.begin() + 1, stxs_got.end());
            return PairV(Value(Quote(stxs_got.front()).eval(e)), Value(Quote(Syntax(temp)).eval(e)));
        }
    } else 
        throw(RuntimeError("Unknown quoted typename"));
}

Value AndVar::eval(Assoc &e) { // and with short-circuit evaluation

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
    if (rand->v_type == V_BOOL) {
        return BooleanV(!dynamic_cast<Boolean*>(rand.get())->b);
    }
    // 非布尔值在Scheme中也被视为真值，not返回#f
    return BooleanV(false);
}

Value If::eval(Assoc &e) {
    // if expression (Scheme: 只有 #f 为假，其余都为真)
    Value valueof_condition = cond->eval(e);
    // 只有当条件是 Boolean 类型且值为 false 时，才返回 alter 分支
    // 其他所有情况（包括 null、数字、符号等）都返回 conseq 分支
    if (valueof_condition->v_type == V_BOOL && 
        dynamic_cast<Boolean*>(valueof_condition.get())->b == false) {
        return alter->eval(e);
    } else {
        return conseq->eval(e);
    }
}

Value Cond::eval(Assoc &env) {
    // cond 表达式求值
    for (const auto &clause : clauses) {
        if (clause.empty()) continue;
        
        // 检查是否为 else 分支
        if (clause[0]->e_type == E_VAR) {
            Var* var_expr = dynamic_cast<Var*>(clause[0].get());
            if (var_expr && var_expr->x == "else") {
                // else 分支：求值所有表达式，返回最后一个
                if (clause.size() == 1) {
                    return VoidV();  // 如果 else 分支没有表达式，返回 void
                }
                Value result = VoidV(); 
                for (size_t i = 1; i < clause.size(); i++) {
                    result = clause[i]->eval(env);
                }
                return result;
            }
        }
        
        // 普通分支：先求值谓词
        Value pred_value = clause[0]->eval(env);
        
        // 只有 #f 是假值
        bool is_true = true;
        if (pred_value->v_type == V_BOOL) {
            Boolean* b = dynamic_cast<Boolean*>(pred_value.get());
            is_true = b->b;
        }
        
        if (is_true) {
            // 求值该分支的所有表达式，返回最后一个
            if (clause.size() == 1) {
                return pred_value;
            }
            Value result = VoidV();
            for (size_t i = 1; i < clause.size(); i++) {
                result = clause[i]->eval(env);
            }
            return result;
        }
    }
    
    // 没有分支匹配，返回 void
    return VoidV();
}

Value Lambda::eval(Assoc &env) { // lambda expression
    Assoc new_env = env;
    return ProcedureV(x, e, new_env);
}

Value Apply::eval(Assoc &e) {
    Value proc_val = rator->eval(e);
    if (proc_val->v_type != V_PROC)
        throw RuntimeError("Attempt to apply a non-procedure");

    Procedure* clos_ptr = dynamic_cast<Procedure*>(proc_val.get());
    
    // 直接使用闭包的环境，然后为参数添加绑定
    // 关键修改：确保我们修改的是真正的闭包环境
    std::vector<Value> args;
    for (int i = 0; i < rand.size(); i++) {
        args.push_back(rand[i]->eval(e));
    }

    if (args.size() != clos_ptr->parameters.size()){
        throw RuntimeError("Wrong number of arguments");
    }
        

    // 在闭包环境基础上添加参数绑定
    Assoc param_env = clos_ptr->env;
    for (int i = 0; i < clos_ptr->parameters.size(); i++) {
        param_env = extend(clos_ptr->parameters[i], args[i], param_env);
    }

    // 执行函数体
    return clos_ptr->e->eval(param_env);
}

Value Define::eval(Assoc &env) {
    // 检查是否试图重新定义primitive函数
    if (primitives.count(var) || reserved_words.count(var)) {
        throw RuntimeError("Cannot redefine primitive: " + var);
    }
    
    // 为了支持递归函数，先在环境中创建一个占位符绑定
    env = extend(var, Value(nullptr), env);
    
    // 计算表达式的值（现在环境中已经有了该变量的绑定）
    Value val = e->eval(env);
    
    // 更新绑定为实际值
    modify(var, val, env);
    
    // define 返回 void
    return VoidV();
}

Value Let::eval(Assoc &env) {
    Assoc new_env = env;
    std::vector<std::pair<std::string, Value>> tobind;
    for (auto binding : bind) {
        tobind.push_back({binding.first, binding.second->eval(env)});
    }
    for (auto binding : tobind) {
        new_env = extend(binding.first, binding.second, new_env);
    }
    return body->eval(new_env);
}

Value Letrec::eval(Assoc &env) {
    // 1. 在当前作用域的基础上创建一个新作用域 env1
    Assoc env1 = env;

    // 2. 将 var* 与 Value(nullptr) 绑定并引入 env1
    for (const auto &binding : bind) {
        env1 = extend(binding.first, Value(nullptr), env1);
    }

    std::vector<std::pair<std::string,Value>> bindings;

    // 3. 在 env1 下对 expr* 求值
    for (const auto &binding : bind) {
        bindings.push_back(std::make_pair(binding.first, binding.second->eval(env1)));
    }

    // 4. 在 env1 的基础上创建一个新作用域 env2
    Assoc env2 = env1;

    // 5. 将 var* 与其对应的值绑定并引入 env2
    for (const auto &binding: bindings) {
        modify(binding.first, binding.second, env2);
    }

    // 6. 最后在 env2 下对 body 求值
    return body->eval(env2);
}

Value Set::eval(Assoc &env) {
    // 检查变量是否存在
    Value var_value = find(var, env);
    if (var_value.get() == nullptr) {
        throw RuntimeError("Undefined variable in set!: " + var);
    }
    
    // 计算新值
    Value new_val = e->eval(env);
    
    // 修改环境中的变量值
    modify(var, new_val, env);
    
    // set! 返回 void
    return VoidV();
}

Value Display::evalRator(const Value &rand) { // display function
    if (rand->v_type == V_STRING) {
        // 对于字符串，输出内容但不包括引号
        String* str_ptr = dynamic_cast<String*>(rand.get());
        std::cout << str_ptr->s;
    } else {
        // 对于其他类型，使用标准显示方法
        rand->show(std::cout);
    }
    
    return VoidV();
}