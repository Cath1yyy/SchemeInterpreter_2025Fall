#include "Def.hpp"
#include "syntax.hpp"
#include "expr.hpp"
#include "value.hpp"
#include "RE.hpp"
#include <sstream>
#include <iostream>
#include <map>

extern std::map<std::string, ExprType> primitives;
extern std::map<std::string, ExprType> reserved_words;

bool isExplicitVoidCall(Expr expr) {
    MakeVoid* make_void_expr = dynamic_cast<MakeVoid*>(expr.get());
    if (make_void_expr != nullptr) {
        return true;
    }
    
    Apply* apply_expr = dynamic_cast<Apply*>(expr.get());
    if (apply_expr != nullptr) {
        Var* var_expr = dynamic_cast<Var*>(apply_expr->rator.get());
        if (var_expr != nullptr && var_expr->x == "void") {
            return true;
        }
    }
    
    Begin* begin_expr = dynamic_cast<Begin*>(expr.get());
    if (begin_expr != nullptr && !begin_expr->es.empty()) {
        return isExplicitVoidCall(begin_expr->es.back());
    }
    
    If* if_expr = dynamic_cast<If*>(expr.get());
    if (if_expr != nullptr) {
        return isExplicitVoidCall(if_expr->conseq) || isExplicitVoidCall(if_expr->alter);
    }
    
    Cond* cond_expr = dynamic_cast<Cond*>(expr.get());
    if (cond_expr != nullptr) {
        for (const auto& clause : cond_expr->clauses) {
            if (clause.size() > 1 && isExplicitVoidCall(clause.back())) {
                return true;
            }
        }
    }
    
    return false;
}

/**
 * @brief Batch processing of multiple define statements supporting mutual recursion
 */
Value evaluateDefineGroup(const std::vector<std::pair<std::string, Expr>>& defines, Assoc &env) {
    // 第一阶段：为所有变量创建占位符绑定
    for (const auto& def : defines) {
        if (primitives.count(def.first) || reserved_words.count(def.first)) {
            throw RuntimeError("Cannot redefine primitive: " + def.first);
        }
        env = extend(def.first, Value(nullptr), env);
    }
    
    // 第二阶段：求值所有表达式并更新绑定
    Value last_result = VoidV();
    for (const auto& def : defines) {
        Value val = def.second->eval(env);
        modify(def.first, val, env);
        last_result = VoidV(); // define 总是返回 void
    }
    
    return last_result;
}

void REPL(){
    // read - evaluation - print loop with define grouping
    Assoc global_env = empty();
    std::vector<std::pair<std::string, Expr>> pending_defines;
    
    while (1){
        #ifndef ONLINE_JUDGE
            std::cout << "scm> ";
        #endif
        Syntax stx = readSyntax(std::cin); // read
        try{
            Expr expr = stx->parse(global_env); // parse
            
            // 检查是否是 define 表达式
            Define* define_expr = dynamic_cast<Define*>(expr.get());
            if (define_expr != nullptr) {
                // 收集 define 表达式
                pending_defines.push_back({define_expr->var, define_expr->e});
                // 不立即求值，继续读取下一个表达式
                continue;
            } else {
                // 不是 define 表达式
                // 如果有待处理的 define，先批量处理它们
                if (!pending_defines.empty()) {
                    evaluateDefineGroup(pending_defines, global_env);
                    pending_defines.clear();
                }
                
                // 处理当前的非 define 表达式
                Value val = expr->eval(global_env);
                if (val->v_type == V_TERMINATE)
                    break;
                
                // 简化的显示逻辑：
                // 如果结果是 void，只有在显式调用 (void) 或在允许的嵌套结构中时才显示
                if (val->v_type == V_VOID) {
                    if (isExplicitVoidCall(expr)) {
                        val->show(std::cout);
                        puts("");
                    }
                    // 其他返回 void 的表达式不输出任何内容
                } else {
                    // 非 void 结果正常显示
                    val->show(std::cout);
                    puts("");
                }
            }
        }
        catch (const RuntimeError &RE){
            // 如果出错，清空待处理的 define
            pending_defines.clear();
            std::cout << "RuntimeError";
            puts("");
        }
    }
    
    // 如果程序结束时还有待处理的 define，处理它们
    if (!pending_defines.empty()) {
        try {
            evaluateDefineGroup(pending_defines, global_env);
        } catch (const RuntimeError &RE) {
            std::cout << "RuntimeError in final defines";
            puts("");
        }
    }
}


int main(int argc, char *argv[]) {
    REPL();
    return 0;
}