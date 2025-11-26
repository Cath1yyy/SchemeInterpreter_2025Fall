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

// 检查是否是应该输出结果的情况
bool shouldOutputValue(Expr expr, Value val) {
    // 如果是显式 void 调用，总是输出
    if (isExplicitVoidCall(expr)) {
        return true;
    }
    
    // 如果是 void 值但不是显式调用，不输出
    if (val->v_type == V_VOID) {
        return false;
    }
    
    // 如果是终止信号，不输出
    if (val->v_type == V_TERMINATE) {
        return false;
    }
    
    // 检查是否是特殊形式，这些通常不应该输出结果
    if (dynamic_cast<Define*>(expr.get()) != nullptr ||
        dynamic_cast<Set*>(expr.get()) != nullptr) {
        return false;
    }
    
    // 其他情况正常输出
    return true;
}

void REPL(){
    // read - evaluation - print loop
    Assoc global_env = empty();

    

    while (1){
        #ifndef ONLINE_JUDGE
            std::cout << "scm> ";
        #endif
        Syntax stx = readSyntax(std :: cin); // read
        try{
            Expr expr = stx -> parse(global_env); // parse
            // stx -> show(std :: cout); // syntax print
            Value val = expr -> eval(global_env);
            if (val -> v_type == V_TERMINATE)
                break;
            // 只有应该输出时才输出
            if (shouldOutputValue(expr, val)) {
                val -> show(std :: cout); // value print
            }
            //val -> show(std :: cout); // value print
        }
        catch (const RuntimeError &RE){
            // std :: cout << RE.message();
            std :: cout << "RuntimeError";
        }
        puts("");
    }
}


int main(int argc, char *argv[]) {
    REPL();
    return 0;
}
