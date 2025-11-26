/**
 * @file parser.cpp
 * @brief Parsing implementation for Scheme syntax tree to expression tree conversion
 * 
 * This file implements the parsing logic that converts syntax trees into
 * expression trees that can be evaluated.
 * primitive operations, and function applications.
 */

#include "RE.hpp"
#include "Def.hpp"
#include "syntax.hpp"
#include "value.hpp"
#include "expr.hpp"
#include <map>
#include <string>
#include <iostream>

#define mp make_pair
using std::string;
using std::vector;
using std::pair;

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

/**
 * @brief Default parse method (should be overridden by subclasses)
 */
Expr Syntax::parse(Assoc &env) {
    throw RuntimeError("Unimplemented parse method");
}

Expr Number::parse(Assoc &env) {
    return Expr(new Fixnum(n));
}

Expr RationalSyntax::parse(Assoc &env) {  //check later
    //TODO: complete the rational parser
    return Expr(new RationalNum(numerator, denominator));
}

Expr SymbolSyntax::parse(Assoc &env) {
    return Expr(new Var(s));
}

Expr StringSyntax::parse(Assoc &env) {
    return Expr(new StringExpr(s));
}

Expr TrueSyntax::parse(Assoc &env) {
    return Expr(new True());
}

Expr FalseSyntax::parse(Assoc &env) {
    return Expr(new False());
}

Expr List::parse(Assoc &env) {
    if (stxs.empty()) {
        return Expr(new Quote(Syntax(new List())));
    }

    //TODO: check if the first element is a symbol
    //If not, use Apply function to package to a closure;
    //If so, find whether it's a variable or a keyword;
    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {

        //TODO
        // 第一个元素不是符号，解析为函数应用
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), args));

    }else{
        string op = id->s;
        if (find(op, env).get() != nullptr) {

            //TODO
            // 在环境中找到变量，解析为函数应用
            vector<Expr> args;
            for (size_t i = 1; i < stxs.size(); i++) {
                args.push_back(stxs[i]->parse(env));
            }
            return Expr(new Apply(Expr(new Var(op)), args));

        }
            if (primitives.count(op) != 0) {
            vector<Expr> parameters;

            //TODO
            for (size_t i = 1; i < stxs.size(); i++) {
                parameters.push_back(stxs[i]->parse(env));
            }

        
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            /*if (parameters.size() == 2) {
                return Expr(new Plus(parameters[0], parameters[1])); 
            } else {
                throw RuntimeError("Wrong number of arguments for +");
            }*/
           return Expr(new PlusVar(parameters));  // 总是使用可变参数版本
        } else if (op_type == E_MINUS) {

            //TODO
            /*if (parameters.size() == 2) {
                return Expr(new Minus(parameters[0], parameters[1]));
            } else {
                return Expr(new MinusVar(parameters));
            }*/
           return Expr(new MinusVar(parameters));  // 总是使用可变参数版本

        } else if (op_type == E_MUL) {

            //TODO
            /*if (parameters.size() == 2) {
                return Expr(new Mult(parameters[0], parameters[1]));
            } else {
                return Expr(new MultVar(parameters));
            }*/
           return Expr(new MultVar(parameters));  // 总是使用可变参数版本

        } else if (op_type == E_DIV) {

            //TODO
            /*if (parameters.size() == 2) {
                return Expr(new Div(parameters[0], parameters[1]));
            } else {
                return Expr(new DivVar(parameters));
            }*/
            return Expr(new DivVar(parameters));  // 总是使用可变参数版本

        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {

            //TODO
            if (parameters.size() == 2) {
                return Expr(new Less(parameters[0], parameters[1]));
            } else {
                return Expr(new LessVar(parameters));
            }

        } else if (op_type == E_LE) {

            //TODO
            if (parameters.size() == 2) {
                return Expr(new LessEq(parameters[0], parameters[1]));
            } else {
                return Expr(new LessEqVar(parameters));
            }

        } else if (op_type == E_EQ) {

            //TODO
            if (parameters.size() == 2) {
                return Expr(new Equal(parameters[0], parameters[1]));
            } else {
                return Expr(new EqualVar(parameters));
            }

        } else if (op_type == E_GE) {

            //TODO
            if (parameters.size() == 2) {
                return Expr(new GreaterEq(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterEqVar(parameters));
            }

        } else if (op_type == E_GT) {

            //TODO
            if (parameters.size() == 2) {
                return Expr(new Greater(parameters[0], parameters[1]));
            } else {
                return Expr(new GreaterVar(parameters));
            }

        } else if (op_type == E_CONS) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for cons");
            }
            return Expr(new Cons(parameters[0], parameters[1]));
        } else if (op_type == E_CAR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for car");
            }
            return Expr(new Car(parameters[0]));
        } else if (op_type == E_CDR) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for cdr");
            }
            return Expr(new Cdr(parameters[0]));
        } else if (op_type == E_SETCAR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-car!");
            }
            return Expr(new SetCar(parameters[0], parameters[1]));
        } else if (op_type == E_SETCDR) {
            if (parameters.size() != 2) {
                throw RuntimeError("Wrong number of arguments for set-cdr!");
                }
            return Expr(new SetCdr(parameters[0], parameters[1]));
        } else if (op_type == E_NOT) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for not");
            }
            return Expr(new Not(parameters[0]));
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else if (op_type == E_BOOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for boolean?");
            }
            return Expr(new IsBoolean(parameters[0]));
        } else if (op_type == E_INTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for number?");
            }
            return Expr(new IsFixnum(parameters[0]));
        } else if (op_type == E_NULLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for null?");
            }
            return Expr(new IsNull(parameters[0]));
        } else if (op_type == E_PAIRQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for pair?");
            }
            return Expr(new IsPair(parameters[0]));
        } else if (op_type == E_PROCQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for procedure?");
            }
            return Expr(new IsProcedure(parameters[0]));
        } else if (op_type == E_SYMBOLQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for symbol?");
            }
            return Expr(new IsSymbol(parameters[0]));
        } else if (op_type == E_STRINGQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for string?");
            }
            return Expr(new IsString(parameters[0]));
        } else if (op_type == E_LISTQ) {
            if (parameters.size() != 1) {
                throw RuntimeError("Wrong number of arguments for list?");
            }
            return Expr(new IsList(parameters[0]));
        } else {

            //TODO
            // 其他原始操作，解析为函数应用
            vector<Expr> args;
            for (size_t i = 1; i < stxs.size(); i++) {
                args.push_back(stxs[i]->parse(env));
            }
            return Expr(new Apply(Expr(new Var(op)), args));

        }
    }

    if (reserved_words.count(op) != 0) {

        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }
        
    	switch (reserved_words[op]) {
			//TODO: TO COMPLETE THE reserve_words PARSER LOGIC
            case E_BEGIN: {
                return Expr(new Begin(parameters));
            }
            case E_QUOTE: {
                if (parameters.size() != 1) {
                    throw RuntimeError("Wrong number of arguments for quote");
                }
                // 注意：quote的参数应该是语法对象，不是表达式
                // 这里需要特殊处理，因为参数不应该被求值
                if (stxs.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for quote");
                }
                return Expr(new Quote(stxs[1]));
            }
            case E_IF: {
                if (parameters.size() < 2 || parameters.size() > 3) {
                    throw RuntimeError("Wrong number of arguments for if");
                }
                Expr alter_expr = parameters.size() == 3 ? parameters[2] : Expr(nullptr);
                return Expr(new If(parameters[0], parameters[1], alter_expr));
            }
            case E_COND: {
                vector<vector<Expr>> clauses;
                for (size_t i = 1; i < stxs.size(); i++) {
                    List* clause_list = dynamic_cast<List*>(stxs[i].get());
                    if (!clause_list) {
                        throw RuntimeError("cond clause must be a list");
                    }
                    vector<Expr> clause_exprs;
                    for (auto& clause_stx : clause_list->stxs) {
                        clause_exprs.push_back(clause_stx->parse(env));
                    }
                    clauses.push_back(clause_exprs);
                }
                return Expr(new Cond(clauses));
            }
            case E_LAMBDA: {
                // lambda 函数定义
                if (parameters.size() < 2) {
                    throw RuntimeError("Wrong number of arguments for lambda");
                }
                // 第一个参数应该是参数列表
                List* param_list = dynamic_cast<List*>(stxs[1].get());
                if (!param_list) {
                    throw RuntimeError("Lambda parameters must be a list");
                }
                vector<string> params;
                for (auto& param_stx : param_list->stxs) {
                    SymbolSyntax* param_sym = dynamic_cast<SymbolSyntax*>(param_stx.get());
                    if (!param_sym) {
                        throw RuntimeError("Lambda parameter must be a symbol");
                    }
                    params.push_back(param_sym->s);
                }
                // 剩下的参数是函数体
                if (stxs.size() < 3) {
                    throw RuntimeError("Lambda must have a body");
                }
                // 解析所有函数体表达式
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(env));
                }
                // 如果函数体有多个表达式，用Begin包装，否则直接使用单个表达式
                Expr body = body_exprs.size() == 1 ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Lambda(params, body));
            }
            case E_DEFINE: {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for define");
                }
                SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!var_sym) {
                    throw RuntimeError("Define variable must be a symbol");
                }
                return Expr(new Define(var_sym->s, parameters[1]));
            }
            case E_LET: {
                // let 局部绑定
                if (parameters.size() < 2) {
                    throw RuntimeError("Wrong number of arguments for let");
                }
                // 第一个参数是绑定列表
                List* bind_list = dynamic_cast<List*>(stxs[1].get());
                if (!bind_list) {
                    throw RuntimeError("Let bindings must be a list");
                }
                vector<pair<string, Expr>> bindings;
                for (auto& bind_stx : bind_list->stxs) {
                    List* bind_pair = dynamic_cast<List*>(bind_stx.get());
                    if (!bind_pair || bind_pair->stxs.size() != 2) {
                        throw RuntimeError("Let binding must be a pair (variable value)");
                    }
                    SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(bind_pair->stxs[0].get());
                    if (!var_sym) {
                        throw RuntimeError("Let variable must be a symbol");
                    }
                    Expr value_expr = bind_pair->stxs[1]->parse(env);
                    bindings.push_back(mp(var_sym->s, value_expr));
                }
                // 剩下的参数是函数体
                if (stxs.size() < 3) {
                    throw RuntimeError("Let must have a body");
                }
                // 解析所有函数体表达式
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(env));
                }
                // 如果函数体有多个表达式，用Begin包装，否则直接使用单个表达式
                Expr body = body_exprs.size() == 1 ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Let(bindings, body));
            }
            case E_LETREC: {
                // letrec 递归局部绑定
                if (parameters.size() < 2) {
                    throw RuntimeError("Wrong number of arguments for letrec");
                }
                // 第一个参数是绑定列表
                List* bind_list = dynamic_cast<List*>(stxs[1].get());
                if (!bind_list) {
                    throw RuntimeError("Letrec bindings must be a list");
                }
                vector<pair<string, Expr>> bindings;
                for (auto& bind_stx : bind_list->stxs) {
                    List* bind_pair = dynamic_cast<List*>(bind_stx.get());
                    if (!bind_pair || bind_pair->stxs.size() != 2) {
                        throw RuntimeError("Letrec binding must be a pair (variable value)");
                    }
                    SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(bind_pair->stxs[0].get());
                    if (!var_sym) {
                        throw RuntimeError("Letrec variable must be a symbol");
                    }
                    Expr value_expr = bind_pair->stxs[1]->parse(env);
                    bindings.push_back(mp(var_sym->s, value_expr));
                }
                // 剩下的参数是函数体
                if (stxs.size() < 3) {
                    throw RuntimeError("Letrec must have a body");
                }
                // 解析所有函数体表达式
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(env));
                }
                // 如果函数体有多个表达式，用Begin包装，否则直接使用单个表达式
                Expr body = body_exprs.size() == 1 ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Letrec(bindings, body));
            }
            case E_SET: {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for set!");
                }
                SymbolSyntax* var_sym = dynamic_cast<SymbolSyntax*>(stxs[1].get());
                if (!var_sym) {
                    throw RuntimeError("Set! variable must be a symbol");
                }
                return Expr(new Set(var_sym->s, parameters[1]));
            }
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    //default: use Apply to be an expression
    //TODO: TO COMPLETE THE PARSER LOGIC
    vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(Expr(new Var(op)), args));
}
}
