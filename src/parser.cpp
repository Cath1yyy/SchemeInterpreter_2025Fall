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

    SymbolSyntax *id = dynamic_cast<SymbolSyntax*>(stxs[0].get());
    if (id == nullptr) {
        // 不是符号，解析为函数应用
        vector<Expr> args;
        for (size_t i = 1; i < stxs.size(); i++) {
            args.push_back(stxs[i]->parse(env));
        }
        return Expr(new Apply(stxs[0]->parse(env), args));
    } else {
        string op = id->s;

        // 关键修复：使用find检查环境绑定
        Value env_value = find(op, env);
        if (env_value.get() != nullptr) {
            // 在环境中找到了这个符号，当作普通函数应用
            vector<Expr> args;
            for (size_t i = 1; i < stxs.size(); i++) {
                args.push_back(stxs[i]->parse(env));
            }
            return Expr(new Apply(Expr(new Var(op)), args));
        }
    // 检查是否为库函数
    if (primitives.count(op) != 0) {
        vector<Expr> parameters;
        for (int i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i].get()->parse(env));
        }
        
        // 特殊处理多参数算术运算符
        ExprType op_type = primitives[op];
        if (op_type == E_PLUS) {
            // PlusVar支持任意数量参数
            return Expr(new PlusVar(parameters)); 
        } else if (op_type == E_MINUS) {
            return Expr(new MinusVar(parameters));
        } else if (op_type == E_MUL) {
            return Expr(new MultVar(parameters));
        } else if (op_type == E_DIV) {
            return Expr(new DivVar(parameters));
        } else if (op_type == E_MODULO) {
            if (parameters.size() != 2) {  //检查参数数量是否正确
                throw RuntimeError("Wrong number of arguments for modulo");
            }
            return Expr(new Modulo(parameters[0], parameters[1]));
        } else if (op_type == E_LIST) {
            // list支持任意数量的参数
            return Expr(new ListFunc(parameters));
        } else if (op_type == E_LT) {
            return Expr(new LessVar(parameters));
        } else if (op_type == E_LE) {
            return Expr(new LessEqVar(parameters));
        } else if (op_type == E_EQ) {
            return Expr(new EqualVar(parameters));
        } else if (op_type == E_GE) {
            return Expr(new GreaterEqVar(parameters));
        } else if (op_type == E_GT) {
            return Expr(new GreaterVar(parameters));
        } else if (op_type == E_AND) {
            return Expr(new AndVar(parameters));
        } else if (op_type == E_OR) {
            return Expr(new OrVar(parameters));
        } else {
            return new Apply(stxs[0].get()->parse(env), parameters);
        }
    }

    if (reserved_words.count(op) != 0) {
        vector<Expr> parameters;
        for (size_t i = 1; i < stxs.size(); i++) {
            parameters.push_back(stxs[i]->parse(env));
        }
    	switch (reserved_words[op]) {
            
			case E_BEGIN:{
             	return Expr(new Begin(parameters));
        	}
			case E_QUOTE:{
				if (parameters.size() != 1) {
                        throw RuntimeError("Wrong number of arguments for quote");
                    }
                    return Expr(new Quote(stxs[1]));  // 直接返回被引用的表达式
			}
			case E_IF:{
				if (parameters.size() != 3) {
                        throw RuntimeError("Wrong number of arguments for if");
                }
                Expr alter_expr = parameters.size() == 3 ? parameters[2] : Expr(nullptr);
                return Expr(new If(parameters[0], parameters[1], alter_expr));
			}
			case E_COND:{
             	if (stxs.size() < 2) {
                    throw RuntimeError("wrong parameter number for cond");
                }
                
             	vector<vector<Expr>> clauses;
             	for (size_t i = 1; i < stxs.size(); i++) {
                 	List* clause_list = dynamic_cast<List*>(stxs[i].get());
                 	if (clause_list == nullptr || clause_list->stxs.empty()) {
                     	throw RuntimeError("Invalid cond clause");
                 	}
                 	vector<Expr> clause_exprs;
                 	for (auto& clause_stx : clause_list->stxs) {
                     	clause_exprs.push_back(clause_stx->parse(env));
                 	}
                 	clauses.push_back(clause_exprs);
             	}
             	return Expr(new Cond(clauses));
        	}
			case E_LAMBDA:{
            	if (parameters.size() < 2) {
                    throw RuntimeError("Wrong number of arguments for lambda");
                }
                std::vector<std::string> vars;
                List* param_list = dynamic_cast<List*>(stxs[1].get());
                    if (!param_list) {
                        throw RuntimeError("Lambda parameters must be a list");
                    }
                Assoc New_env = env; // 创建lambda的环境 - 关键修复：先创建环境再解析参数
            	for (int i = 0; i < param_list->stxs.size(); i++) {
                    if (auto tmp_var = dynamic_cast<Var*>(param_list->stxs[i].get()->parse(env).get())) {
                        vars.push_back(tmp_var->x);
                        New_env = extend(tmp_var->x, NullV(), New_env);
                    } else {
                        throw RuntimeError("Invalid input of variable");
                    }	
                }
                	
                // 处理多个body表达式
                if (stxs.size() == 3) {
                	// 单个body表达式
                	return Expr(new Lambda(vars, stxs[2].get()->parse(New_env)));
                } else {
                	// 多个body表达式，包装在Begin中
                	vector<Expr> body_exprs;
                	for (size_t i = 2; i < stxs.size(); i++) {
                		body_exprs.push_back(stxs[i]->parse(New_env));
                	}
                	return Expr(new Lambda(vars, Expr(new Begin(body_exprs))));
                }
        	}
			case E_DEFINE:{
				if (stxs.size() < 3) throw RuntimeError("wrong parameter number for define");
			
				// 检查第二个元素是否为List（函数定义语法糖）
				List *func_def = dynamic_cast<List*>(stxs[1].get());
				if (func_def != nullptr) {
					// 语法糖: (define (func-name param1 param2 ...) body...)
					if (func_def->stxs.empty()) {
						throw RuntimeError("Invalid function definition: empty parameter list");
					}
				
					// 第一个元素应该是函数名
					SymbolSyntax *func_name = dynamic_cast<SymbolSyntax*>(func_def->stxs[0].get());
					if (func_name == nullptr) {
						throw RuntimeError("Invalid function name in define");
					}
				
					// 提取参数列表
					vector<string> param_names;
					for (size_t i = 1; i < func_def->stxs.size(); i++) {
						SymbolSyntax *param = dynamic_cast<SymbolSyntax*>(func_def->stxs[i].get());
						if (param == nullptr) {
							throw RuntimeError("Invalid parameter in function definition");
						}
						param_names.push_back(param->s);
					}
				
					// 创建lambda表达式，支持多个body表达式
					if (stxs.size() == 3) {
						// 单个body表达式
						Expr lambda_expr = Expr(new Lambda(param_names, stxs[2]->parse(env)));
						return Expr(new Define(func_name->s, lambda_expr));
					} else {
						// 多个body表达式，包装在Begin中
						vector<Expr> body_exprs;
						for (size_t i = 2; i < stxs.size(); i++) {
							body_exprs.push_back(stxs[i]->parse(env));
						}
						Expr lambda_expr = Expr(new Lambda(param_names, Expr(new Begin(body_exprs))));
						return Expr(new Define(func_name->s, lambda_expr));
					}
				} else {
					// 原有语法: (define var-name expression)
					if (stxs.size() != 3){
                        throw RuntimeError("Wrong number of arguments for define");
                    }
                    
					SymbolSyntax *var_id = dynamic_cast<SymbolSyntax*>(stxs[1].get());
					if (var_id == nullptr) {throw RuntimeError("Invalid define variable");}
					return Expr(new Define(var_id->s, stxs[2]->parse(env)));
				}
			}
        	case E_LET:{
            	if (stxs.size() != 3) throw RuntimeError("Wrong number of argumentsfor let");
        		vector<pair<string, Expr>> binded_vector;
            	List *binder_list_ptr = dynamic_cast<List*>(stxs[1].get());
            	if (binder_list_ptr == nullptr) throw RuntimeError("Invalid let binding list");

            	Assoc local_env = env; // 创建新的环境
                for (int i = 0; i < binder_list_ptr->stxs.size(); i++) {
                    auto pair_it = dynamic_cast<List*>(binder_list_ptr->stxs[i].get());
                    if ((pair_it == nullptr)||(pair_it->stxs.size() != 2)) {
                        throw RuntimeError("Invalid let binding list");
                    }
                    auto Identifiers = dynamic_cast<SymbolSyntax*>(pair_it->stxs.front().get());
                    if (Identifiers == nullptr) {
                        throw RuntimeError("Invalid input of identifier");
                    }
                    Expr temp_expr = pair_it->stxs.back().get()->parse(env);
                    local_env = extend(Identifiers->s, NullV(), local_env);
                    pair<string, Expr> tmp_pair = std::make_pair(Identifiers->s, temp_expr);
                    binded_vector.push_back(tmp_pair);
                }
             	return Expr(new Let(binded_vector, stxs[2]->parse(local_env))); // 使用 local_env
        	}
        	case E_LETREC:{
    			if (stxs.size() != 3) throw RuntimeError("Wrong number of arguments for letrec");
    			vector<pair<string, Expr>> binded_vector;
    			List *binder_list_ptr = dynamic_cast<List*>(stxs[1].get());
    			if (binder_list_ptr == nullptr) {
                    throw RuntimeError("Invalid letrec binding list");
                }
    			// 创建新的环境用于解析
    			Assoc temp_env = env;
    			// 第一次遍历：收集所有变量名并在临时环境中绑定为 null
    			for (auto &stx_tobind_raw : binder_list_ptr->stxs) {
        			List *stx_tobind = dynamic_cast<List*>(stx_tobind_raw.get());
        			if (stx_tobind == nullptr || stx_tobind->stxs.size() != 2) {
                        throw RuntimeError("Invalid letrec binding");
                    }
        			SymbolSyntax *temp_id = dynamic_cast<SymbolSyntax*>(stx_tobind->stxs[0].get());
        			if (temp_id == nullptr) {
                        throw RuntimeError("Invalid letrec binding variable");
                    }
        			// 在临时环境中绑定变量，初始值为 null
        			temp_env = extend(temp_id->s, NullV(), temp_env);
    			}
    			// 第二次遍历：使用包含所有变量的环境解析表达式
    			for (auto &stx_tobind_raw : binder_list_ptr->stxs) {
        			List *stx_tobind = dynamic_cast<List*>(stx_tobind_raw.get());
        			SymbolSyntax *temp_id = dynamic_cast<SymbolSyntax*>(stx_tobind->stxs[0].get());
        			// 在包含所有变量的环境中解析表达式
        			Expr temp_store = stx_tobind->stxs[1]->parse(temp_env);
        			binded_vector.push_back(std::make_pair(temp_id->s, temp_store));
    			}
    			// 使用同样的环境解析 body
    			return Expr(new Letrec(binded_vector, stxs[2]->parse(temp_env)));
			}
			case E_SET:{
				if (stxs.size() != 3){
                    throw RuntimeError("wrong parameter number for set!");
                }
                
				SymbolSyntax *var_id = dynamic_cast<SymbolSyntax*>(stxs[1].get());
				if (var_id == nullptr) {
                    throw RuntimeError("Invalid set! variable");
                }
				return Expr(new Set(var_id->s, stxs[2]->parse(env)));
			}
        	default:
            	throw RuntimeError("Unknown reserved word: " + op);
    	}
    }

    // 默认情况：构造 Apply 表达式
    Expr opexpr = stxs[0]->parse(env);
    vector<Expr> to_expr;
    for (size_t i = 1; i < stxs.size(); i++) {
        to_expr.push_back(stxs[i]->parse(env));
    }
    return Expr(new Apply(opexpr, to_expr));
}
}