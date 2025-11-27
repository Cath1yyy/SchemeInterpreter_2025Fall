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
#include <set>

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
    std::set<std::string> shadow;
    //=========================================
    // 调试输出：显示正在解析的列表
    //std::cerr << "DEBUG: Parsing list with " << stxs.size() << " elements" << std::endl;
    /*for (size_t i = 0; i < stxs.size(); i++) {
        SymbolSyntax* sym = dynamic_cast<SymbolSyntax*>(stxs[i].get());
        if (sym) {
            std::cerr << "  [" << i << "]: Symbol '" << sym->s << "'" << std::endl;
        } else {
            std::cerr << "  [" << i << "]: Non-symbol syntax" << std::endl;
        }
    }*/
    //=========================================

    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // 第一个元素不是符号，解析为函数应用

        //======================================
        //std::cerr << "DEBUG: First element is not a symbol, treating as application" << std::endl;
        //======================================

        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), args));
    } else {
        string op = id->s;

        //====================================
        //std::cerr << "DEBUG: First element is symbol: '" << op << "'" << std::endl;
        //====================================

        // 首先检查是否在环境中（包括局部绑定的变量）
        if (find(op, env).get() != nullptr) {
            // 在环境中找到变量，解析为函数应用

            //=================================
            //std::cerr << "DEBUG: Found '" << op << "' in environment" << std::endl;
            //=================================

            vector<Expr> args;
            for (size_t i = 1; i < stxs.size(); i++) {
                args.push_back(stxs[i]->parse(env));
            }
            return Expr(new Apply(Expr(new Var(op)), args));
        }
        else{

            //=================================
            //std::cerr << "DEBUG: '" << op << "' NOT found in environment" << std::endl;
            //=================================

        }

        // 然后检查是否是特殊形式（只在语法位置）
        if (reserved_words.count(op) != 0 && find(op, env).get() == nullptr) {
            // 处理特殊形式
            
            //=================================
            //std::cerr << "DEBUG: '" << op << "' is a reserved word" << std::endl;
            //=================================

            vector<Expr> parameters;
            for (size_t i = 1; i < stxs.size(); i++) {
                parameters.push_back(stxs[i]->parse(env));
            }
            
            // 根据操作符类型处理特殊形式
            switch (reserved_words[op]) {
                case E_BEGIN: {
                    return Expr(new Begin(parameters));
                }
                case E_QUOTE: {
                    if (parameters.size() != 1) {
                        throw RuntimeError("Wrong number of arguments for quote");
                    }
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
    if (parameters.size() < 2) {
        throw RuntimeError("Wrong number of arguments for lambda");
    }
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

    // extend parsing environment so body sees parameters
    Assoc parse_env = env;
    for (auto &p : params) {
        //parse_env = extend(p, Value(nullptr), parse_env);
        parse_env = extend(p, VoidV(), parse_env);
    }

    if (stxs.size() < 3) {
        throw RuntimeError("Lambda must have a body");
    }

    vector<Expr> body_exprs;
    for (size_t i = 2; i < stxs.size(); i++) {
        body_exprs.push_back(stxs[i]->parse(parse_env));
    }

    Expr body = body_exprs.size() == 1 ? body_exprs[0] : Expr(new Begin(body_exprs));
    return Expr(new Lambda(params, body));
}
                case E_DEFINE: {
                    if (parameters.size() < 1) {
                        throw RuntimeError("Wrong number of arguments for define");
                    }
                    List* func_def = dynamic_cast<List*>(stxs[1].get());
                    if (func_def && !func_def->stxs.empty()) {
    SymbolSyntax* func_name_sym = dynamic_cast<SymbolSyntax*>(func_def->stxs[0].get());
    if (func_name_sym) {
        std::string func_name = func_name_sym->s;
        vector<string> params;
        for (size_t i = 1; i < func_def->stxs.size(); i++) {
            SymbolSyntax* param_sym = dynamic_cast<SymbolSyntax*>(func_def->stxs[i].get());
            if (!param_sym) {
                throw RuntimeError("Function parameter must be a symbol");
            }
            params.push_back(param_sym->s);
        }

        // --- build parse-time environment so parameters shadow keywords in body ---
        Assoc parse_env = env;
        for (auto &p : params) {
            parse_env = extend(p, VoidV(), parse_env);
        }

        vector<Expr> body_exprs;
        for (size_t i = 2; i < stxs.size(); i++) {
            body_exprs.push_back(stxs[i]->parse(parse_env));
        }
        Expr body = body_exprs.size() == 1 ? body_exprs[0] : Expr(new Begin(body_exprs));
        Expr lambda_expr(new Lambda(params, body));
        return Expr(new Define(func_name, lambda_expr));
    }
}
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
                    if (parameters.size() < 2) {
                        throw RuntimeError("Wrong number of arguments for let");
                    }
                List* bind_list = dynamic_cast<List*>(stxs[1].get());
                if (!bind_list) {
                    throw RuntimeError("Let bindings must be a list");
                }

                // Step 1: parse all binding expressions first
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
                    string var_name = var_sym->s;

                    Expr value_expr = bind_pair->stxs[1]->parse(env);
                    bindings.push_back(mp(var_name, value_expr));
                }

                // Step 2: extend parsing environment so body can shadow keywords
                Assoc parse_env = env;
                for (auto &b : bindings) {
                    //parse_env = extend(b.first, Value(nullptr), parse_env);
                    parse_env = extend(b.first, VoidV(), parse_env);
                }

                // Step 3: parse body in extended environment
                if (stxs.size() < 3) {
                    throw RuntimeError("Let must have a body");
                }
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(parse_env));
                }

                Expr body = body_exprs.size() == 1 ? body_exprs[0] : Expr(new Begin(body_exprs));
                return Expr(new Let(bindings, body));
            }
                case E_LETREC: {
                if (parameters.size() < 2) {
                    throw RuntimeError("Wrong number of arguments for letrec");
                }
                List* bind_list = dynamic_cast<List*>(stxs[1].get());
                if (!bind_list) {
                    throw RuntimeError("Letrec bindings must be a list");
                }
            
                // Step 1: extend parse env FIRST (letrec: variables visible to all RHS)
                Assoc parse_env = env;
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
                    string var_name = var_sym->s;

                    // Add name first
                    //parse_env = extend(var_name, Value(nullptr), parse_env);
                    parse_env = extend(var_name, VoidV(), parse_env);
                    bindings.push_back(mp(var_name, Expr(nullptr))); // temporary placeholder
                }

                // Step 2: parse RHS using parse_env
                for (size_t i = 0; i < bind_list->stxs.size(); i++) {
                    List* bind_pair = dynamic_cast<List*>(bind_list->stxs[i].get());
                    Expr value_expr = bind_pair->stxs[1]->parse(parse_env);
                    bindings[i].second = value_expr;
                }

                // Step 3: parse body with parse_env
                if (stxs.size() < 3) {
                    throw RuntimeError("Letrec must have a body");
                }
                vector<Expr> body_exprs;
                for (size_t i = 2; i < stxs.size(); i++) {
                    body_exprs.push_back(stxs[i]->parse(parse_env));
                }
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

        // 检查是否是原始操作
        /*if (primitives.count(op) != 0) {

            //std::cerr << "DEBUG: '" << op << "' is a primitive operation" << std::endl;

            vector<Expr> parameters;
            for (size_t i = 1; i < stxs.size(); i++) {
                parameters.push_back(stxs[i]->parse(env));
            }

            ExprType op_type = primitives[op];
            if (op_type == E_PLUS) {
                return Expr(new PlusVar(parameters));
            } else if (op_type == E_MINUS) {
                return Expr(new MinusVar(parameters));
            } else if (op_type == E_MUL) {
                return Expr(new MultVar(parameters));
            } else if (op_type == E_DIV) {
                return Expr(new DivVar(parameters));
            } else if (op_type == E_MODULO) {
                if (parameters.size() != 2) {
                    throw RuntimeError("Wrong number of arguments for modulo");
                }
                return Expr(new Modulo(parameters[0], parameters[1]));
            } else if (op_type == E_LIST) {
                return Expr(new ListFunc(parameters));
            } else if (op_type == E_LT) {
                if (parameters.size() == 2) {
                    return Expr(new Less(parameters[0], parameters[1]));
                } else {
                    return Expr(new LessVar(parameters));
                }
            } else if (op_type == E_LE) {
                if (parameters.size() == 2) {
                    return Expr(new LessEq(parameters[0], parameters[1]));
                } else {
                    return Expr(new LessEqVar(parameters));
                }
            } else if (op_type == E_EQ) {
                if (parameters.size() == 2) {
                    return Expr(new Equal(parameters[0], parameters[1]));
                } else {
                    return Expr(new EqualVar(parameters));
                }
            } else if (op_type == E_GE) {
                if (parameters.size() == 2) {
                    return Expr(new GreaterEq(parameters[0], parameters[1]));
                } else {
                    return Expr(new GreaterEqVar(parameters));
                }
            } else if (op_type == E_GT) {
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
                // 其他原始操作，解析为函数应用
                vector<Expr> args;
                for (size_t i = 1; i < stxs.size(); i++) {
                    args.push_back(stxs[i]->parse(env));
                }
                return Expr(new Apply(Expr(new Var(op)), args));
            }
        }*/
       // 检查是否是原始操作
if (primitives.count(op) != 0) {

    vector<Expr> parameters;
    for (size_t i = 1; i < stxs.size(); i++) {
        parameters.push_back(stxs[i]->parse(env));
    }

    ExprType op_type = primitives[op];

    // 所有 primitive 运算符都统一解析为 Apply
    // 即： (op arg1 arg2 ...) → Apply( Var(op), [args...] )

    switch (op_type) {
        case E_PLUS:
        case E_MINUS:
        case E_MUL:
        case E_DIV:
        case E_MODULO:
        case E_LT:
        case E_LE:
        case E_EQ:
        case E_GE:
        case E_GT:
        case E_LIST:
        case E_CONS:
        case E_CAR:
        case E_CDR:
        case E_SETCAR:
        case E_SETCDR:
        case E_NOT:
        case E_AND:
        case E_OR:
        case E_BOOLQ:
        case E_INTQ:
        case E_NULLQ:
        case E_PAIRQ:
        case E_PROCQ:
        case E_SYMBOLQ:
        case E_STRINGQ:
        case E_LISTQ:
            return Expr(new Apply(Expr(new Var(op)), parameters));

        default:
            // 其他未列出的 primitive 同样作为函数调用处理
            return Expr(new Apply(Expr(new Var(op)), parameters));
    }
}

        // 默认情况：解析为函数应用
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(Expr(new Var(op)), args));
    }
}