/*
 * Copyright 2017 Hyperkernel Authors
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "PyEmitter.hh"
#include "PyLLVMEmitter.hh"
#include "llvm/IR/Operator.h"

#include <sstream>

namespace irpy {

using kwargs_t = llvm::SmallVector<std::tuple<std::string, std::string>, 5>;
using args_t = llvm::SmallVector<std::string, 8>;

template <typename T> std::string print(const T *val)
{
    std::string res;
    llvm::raw_string_ostream stream{res};
    val->print(stream);
    return stream.str();
}

static std::string quote(const std::string &s)
{
    return "'" + s + "'";
}

static std::string nameType(const llvm::Value *val)
{
    return "itypes.parse_type(ctx," + quote(print(val->getType())) + ")";
}

static std::string getPrintingName(const llvm::Value &val, bool strip, const llvm::Module &mod)
{
    std::string res;
    llvm::raw_string_ostream stream{res};
    val.printAsOperand(stream, /* PrintType = */ false, &mod);
    stream.str();

    /* Really hacky way to remove characters that can't be used as function names in pyton */
    if (strip && res.length() > 0 && (res[0] == '%' || res[0] == '@')) {
        res = res.substr(1);
    }
    if (res.length() == 0) {
        llvm::report_fatal_error("Printing name has length zero");
    }

    // . is not valid in python identifier
    std::replace(res.begin(), res.end(), '.', '_');

    /* - is not valid */
    std::replace(res.begin(), res.end(), '-', '_');

    return res;
}

class MetadataVisitor : public llvm::InstVisitor<MetadataVisitor>
{
  private:
    const llvm::Module &module_;
    std::set<const llvm::Metadata *> meta;
    const bool recursive;

  public:
    MetadataVisitor(llvm::Module &module, bool recursive = true)
        : module_(module), recursive(recursive)
    {
    }

    void addMDNode(const llvm::MDNode *node)
    {
        if (meta.find(node) != meta.end())
            return;

        meta.insert(node);

        if (recursive)
            for (unsigned op = 0; op < node->getNumOperands(); op++) {
                auto operand = node->getOperand(op).get();
                if (operand != nullptr) {
                    if (llvm::MDNode *mdop = llvm::dyn_cast<llvm::MDNode>(operand))
                        addMDNode(mdop);
                }
            }
    }

    void visitFunction(const llvm::Function &bb)
    {
        llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 100> v;
        bb.getAllMetadata(v);
        for (const auto &i : v) {
            addMDNode(i.second);
        }
    }

    void visitInstruction(const llvm::Instruction &i)
    {
        llvm::SmallVector<std::pair<unsigned, llvm::MDNode *>, 100> v;
        i.getAllMetadata(v);
        for (const auto &i : v) {
            addMDNode(i.second);
        }
    }

    std::vector<std::pair<int, std::string>> getMetadata(void)
    {
        std::vector<std::pair<int, std::string>> output(0);

        for (const auto &md : this->meta) {
            std::string res;
            llvm::raw_string_ostream stream{res};
            md->print(stream, &this->module_);
            auto line = stream.str();
            auto delim = line.find(" = ");
            auto identifier = std::stoi(line.substr(1, delim));
            output.push_back(std::make_pair(identifier, line.substr(delim + 3)));
        }

        std::sort(output.begin(), output.end());
        return output;
    }
};

class PyInstVisitor : public llvm::InstVisitor<PyInstVisitor>
{
  private:
    PyEmitter &emitter_;
    llvm::Module &module_;

  public:
    PyInstVisitor(PyEmitter &emitter, llvm::Module &module) : emitter_(emitter), module_(module)
    {
    }

    template <typename T> void genPyCallFromInstruction(bool hasReturn, const std::string &fname, T &i, kwargs_t kwargs = {})
    {
        args_t args;
        args.push_back(nameType(&i));
        for (ssize_t j = 0; j < i.getNumOperands(); j++) {
            args.push_back(get(i.getOperand(j)));
            args.push_back(nameType(i.getOperand(j)));
        }

        std::ostringstream metalist_ss;
        metalist_ss << "[";

        MetadataVisitor mv{this->module_, false};
        mv.visitInstruction(i);
        for (const auto &meta : mv.getMetadata()) {
            metalist_ss << "'!" << std::to_string(meta.first) << "',";
        }
        metalist_ss << "]";

        const std::string metalist = metalist_ss.str();

        if (i.hasNoSignedWrap())
            kwargs.push_back({"nsw", "True"});
        if (i.hasNoUnsignedWrap())
            kwargs.push_back({"nuw", "True"});

        auto s = genPyCall(fname, args, kwargs);

        if (hasReturn) {
            emitter_.line(get(&i) + " = " + s);
        } else {
            emitter_.line(s);
        }
    }

    std::string genPyCall(std::string fname, const args_t &args,
                          const kwargs_t &kwargs = {})
    {
        /* these are  python keyword */
        if (fname == "and") {
            fname = "and_";
        } else if (fname == "or") {
            fname = "or_";
        }

        args_t ctx = {"ctx"};
        ctx.insert(ctx.end(), args.begin(), args.end());

        return _genPyCall("irpy." + fname, ctx, kwargs);
    }

    std::string _genPyCall(const std::string &fname, const args_t &args,
                           const kwargs_t &kwargs)
    {
        std::ostringstream call;
        call << fname << "(";
        for (const auto &a : args)
            call << a << ",";
        for (const auto &a : kwargs)
            call << std::get<0>(a) << "=" << std::get<1>(a) << ",";
        call << ")";
        return call.str();
    }

    std::string name(const llvm::Value *val)
    {
        return getPrintingName(*val, false, this->module_);
    }

    std::string get(const llvm::Value *val)
    {
        if (const llvm::Instruction *i = llvm::dyn_cast<llvm::Instruction>(val)) {
            return ("ctx.stack[\"" + name(i) + "\"]");
        } else if (const llvm::Constant *c = llvm::dyn_cast<llvm::Constant>(val)) {
            return this->visitConstant(c);
        } else if (const llvm::Argument *a = llvm::dyn_cast<llvm::Argument>(val)) {
            return ("ctx.stack[\"" + name(a) + "\"]");
        } else if (const llvm::InlineAsm *ia = llvm::dyn_cast<llvm::InlineAsm>(val)) {
            return genPyCall("asm", {quote(ia->getAsmString())});
        }
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
        val->dump();
#endif
        llvm::report_fatal_error("Unhandled value");
    }

    std::string visitConstant(const llvm::Constant *c)
    {
        if (auto ci = llvm::dyn_cast<llvm::ConstantInt>(c)) {
            return visitConstantInt(*ci);
        } else if (auto ce = llvm::dyn_cast<llvm::ConstantExpr>(c)) {
            return visitConstantExpr(ce);
        } else if (auto undef = llvm::dyn_cast<llvm::UndefValue>(c)) {
            return genPyCall("undef", {nameType(undef)});
        } else if (auto undef = llvm::dyn_cast<llvm::ConstantPointerNull>(c)) {
            return genPyCall("constant_pointer_null", {nameType(undef)});
        } else if (auto gv = llvm::dyn_cast<llvm::GlobalValue>(c)) {
            return genPyCall("global_value", {nameType(gv), quote(name(gv))});
        } else if (auto ca = llvm::dyn_cast<llvm::ConstantDataArray>(c)) {
            return genPyCall("constant_data_array", {nameType(ca), quote(name(ca))});
        } else if (auto ca = llvm::dyn_cast<llvm::ConstantArray>(c)) {
            return genPyCall("constant_array", {nameType(ca), quote(name(ca))});
        } else if (auto ca = llvm::dyn_cast<llvm::ConstantAggregateZero>(c)) {
            return genPyCall("constant_aggregate_zero", {nameType(ca), quote(name(ca))});
        } else {
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
            c->dump();
#endif
            llvm::report_fatal_error("Unknown constant type");
        }
    }

    std::string visitConstantInt(const llvm::ConstantInt &c)
    {
        return genPyCall("constant_int",
                         {c.getValue().toString(10, false), std::to_string(c.getBitWidth())});
    }

    std::string visitConstantExpr(const llvm::ConstantExpr *e)
    {
        std::string opstring;
        args_t args;
        args.push_back(nameType(e));
        for (ssize_t i = 0; i < e->getNumOperands(); i++) {
            args.push_back(get(e->getOperand(i)));
            args.push_back(nameType(e->getOperand(i)));
        }

        opstring = e->getOpcodeName();

        if (opstring == "icmp") {
            switch (e->getPredicate()) {
            case llvm::CmpInst::Predicate::ICMP_EQ:
                opstring = "eq";
                break;
            case llvm::CmpInst::Predicate::ICMP_NE:
                opstring = "ne";
                break;
            case llvm::CmpInst::Predicate::ICMP_SLT:
                opstring = "slt";
                break;
            case llvm::CmpInst::Predicate::ICMP_SLE:
                opstring = "sle";
                break;
            case llvm::CmpInst::Predicate::ICMP_SGT:
                opstring = "sgt";
                break;
            case llvm::CmpInst::Predicate::ICMP_SGE:
                opstring = "sge";
                break;
            case llvm::CmpInst::Predicate::ICMP_ULT:
                opstring = "ult";
                break;
            case llvm::CmpInst::Predicate::ICMP_ULE:
                opstring = "ule";
                break;
            case llvm::CmpInst::Predicate::ICMP_UGT:
                opstring = "ugt";
                break;
            case llvm::CmpInst::Predicate::ICMP_UGE:
                opstring = "uge";
                break;
            default:
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
                e->dump();
#endif
                llvm::report_fatal_error("Unknown icmp predicate");
            }
        }

        return genPyCall(opstring, args);
    }

    void visitReturnInst(const llvm::ReturnInst &i)
    {
        switch (i.getNumOperands()) {
        case 0:
            emitter_.line("return");
            break;
        case 1:
            emitter_.line("return " + get(i.getOperand(0)));
            break;
        default:
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
            i.dump();
#endif
            llvm::report_fatal_error(">= 2 return operands");
        }
    }

    void visitBinaryOperator(const llvm::BinaryOperator &i)
    {
        std::string opstring, op1, op2, dst;

        dst = get(&i);
        op1 = get(i.getOperand(0));
        op2 = get(i.getOperand(1));

        opstring = i.getOpcodeName();

        kwargs_t kwargs;
        if (i.hasNoSignedWrap())
            kwargs.push_back({"nsw", "True"});
        if (i.hasNoUnsignedWrap())
            kwargs.push_back({"nuw", "True"});

        if (const auto *peo = llvm::dyn_cast<llvm::PossiblyExactOperator>(&i))
            if (peo->isExact())
                kwargs.push_back({"exact", "True"});

        emitter_.line(dst + " = " +
                      genPyCall(opstring, {
                                              nameType(&i), op1, nameType(i.getOperand(0)), op2,
                                              nameType(i.getOperand(1)),
                                          }, kwargs));
    }

    void visitICmpInst(const llvm::ICmpInst &i)
    {
        std::string opstring, op1, op2, dst;

        dst = get(&i);
        op1 = get(i.getOperand(0));
        op2 = get(i.getOperand(1));

        switch (i.getPredicate()) {
        case llvm::CmpInst::Predicate::ICMP_EQ:
            opstring = "eq";
            break;
        case llvm::CmpInst::Predicate::ICMP_NE:
            opstring = "ne";
            break;
        case llvm::CmpInst::Predicate::ICMP_SLT:
            opstring = "slt";
            break;
        case llvm::CmpInst::Predicate::ICMP_SLE:
            opstring = "sle";
            break;
        case llvm::CmpInst::Predicate::ICMP_SGT:
            opstring = "sgt";
            break;
        case llvm::CmpInst::Predicate::ICMP_SGE:
            opstring = "sge";
            break;
        case llvm::CmpInst::Predicate::ICMP_ULT:
            opstring = "ult";
            break;
        case llvm::CmpInst::Predicate::ICMP_ULE:
            opstring = "ule";
            break;
        case llvm::CmpInst::Predicate::ICMP_UGT:
            opstring = "ugt";
            break;
        case llvm::CmpInst::Predicate::ICMP_UGE:
            opstring = "uge";
            break;
        default:
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
            i.dump();
#endif
            llvm::report_fatal_error("Unhandled predicate");
        }

        emitter_.line(dst + " = " +
                      genPyCall(opstring, {
                                              nameType(&i), op1, nameType(i.getOperand(0)), op2,
                                              nameType(i.getOperand(1)),
                                          }));
    }

    void visitSelectInst(const llvm::SelectInst &i)
    {
        std::string dst, cond, trueval, falseval;
        dst = get(&i);
        cond = get(i.getCondition());
        trueval = get(i.getTrueValue());
        falseval = get(i.getFalseValue());

        emitter_.line(dst + " = " +
                      genPyCall("select", {
                                              nameType(&i), cond, nameType(i.getCondition()),
                                              trueval, nameType(i.getTrueValue()), falseval,
                                              nameType(i.getFalseValue()),
                                          }));
    }

    void visitBranchInst(const llvm::BranchInst &i)
    {
        auto curr_bb = "(\"" + name(i.getParent()) + "\")";
        if (i.isConditional()) {

            auto cond = get(i.getCondition());
            auto true_target =
                "bb_" + getPrintingName(*i.getSuccessor(0), true, this->module_) + curr_bb;
            auto false_target =
                "bb_" + getPrintingName(*i.getSuccessor(1), true, this->module_) + curr_bb;

            emitter_.line("return " + genPyCall("branch", {
                                                              cond, nameType(i.getCondition()),
                                                              "lambda: " + true_target,
                                                              "lambda: " + false_target,
                                                          }));
        } else {
            /* Unconditional branch */
            auto bb_target = getPrintingName(*i.getSuccessor(0), true, this->module_);
            emitter_.line("return bb_" + bb_target + curr_bb);
        }
    }

    void visitPHINode(const llvm::PHINode &i)
    {
        std::ostringstream phimap;
        std::string dst = get(&i);

        phimap << "{";
        for (unsigned j = 0; j < i.getNumIncomingValues(); ++j) {
            auto bb = i.getIncomingBlock(j);
            auto val = i.getIncomingValue(j);
            phimap << " \"" + name(bb) + "\": (lambda : " + get(val) + "),";
        }
        phimap << "}";

        emitter_.line(dst + " = " + phimap.str() + "[pred]()");
    }

    void visitTruncInst(const llvm::TruncInst &i)
    {
        std::string operand, dst;
        dst = get(&i);
        operand = get(i.getOperand(0));
        genPyCallFromInstruction(true, "trunc", i);
    }

    void visitZExtInst(const llvm::ZExtInst &i)
    {
        std::string dst, operand;
        dst = get(&i);
        operand = get(i.getOperand(0));
        genPyCallFromInstruction(true, "zext", i);
    }

    void visitSExtInst(const llvm::SExtInst &i)
    {
        std::string dst, operand;
        dst = get(&i);
        operand = get(i.getOperand(0));
        genPyCallFromInstruction(true, "sext", i);
    }

    void visitLoadInst(const llvm::LoadInst &i)
    {
        genPyCallFromInstruction(true, "load", i);
    }

    void visitStoreInst(const llvm::StoreInst &i)
    {
        genPyCallFromInstruction(false, "store", i);
    }

    void visitAllocaInst(const llvm::AllocaInst &i)
    {
        genPyCallFromInstruction(true, "alloca", i);
    }

    void visitPtrToIntInst(const llvm::PtrToIntInst &i)
    {
        genPyCallFromInstruction(true, "ptr_to_int", i);
    }

    void visitIntToPtrInst(const llvm::IntToPtrInst &i)
    {
        genPyCallFromInstruction(true, "int_to_ptr", i);
    }

    void visitBitCastInst(const llvm::BitCastInst &i)
    {
        genPyCallFromInstruction(true, "bitcast", i);
    }

    void visitGetElementPtrInst(const llvm::GetElementPtrInst &i)
    {
        kwargs_t kwargs;
        if (i.isInBounds())
            kwargs.push_back({"inbounds", "True"});
        genPyCallFromInstruction(true, "get_element_ptr", i, kwargs);
    }

    void visitSwitchInst(const llvm::SwitchInst &i)
    {
        args_t args;
        auto curr_bb = "(\"" + name(i.getParent()) + "\")";

        args.push_back(get(i.getCondition()));
        args.push_back(nameType(i.getCondition()));
        args.push_back("lambda: bb_" + getPrintingName(*i.getDefaultDest(), true, this->module_) +
                       curr_bb);

        for (const auto &c : i.cases()) {
            auto arg = "(" + get(c.getCaseValue()) + ",";
            arg += nameType(c.getCaseValue());
            arg += ", lambda: bb_" + getPrintingName(*c.getCaseSuccessor(), true, this->module_);
            arg += curr_bb + ")";
            args.push_back(arg);
        }

        emitter_.line("return " + genPyCall("switch", args));
    }

    void visitDbgDeclareInst(const llvm::DbgDeclareInst &i) const
    {
        // genPyCallFromInstruction(false ,"debug_declare", i);
    }

    void visitDbgValueInst(const llvm::DbgValueInst &i) const
    {
        // genPyCallFromInstruction(false ,"debug_value", i);
    }

    void visitDbgInfoIntrinsic(const llvm::DbgInfoIntrinsic &i) const
    {
        // genPyCallFromInstruction(false ,"debug_info_intrinsic", i);
    }

    void visitCallInst(const llvm::CallInst &i)
    {
        bool has_return = i.getType()->getTypeID() != llvm::Type::TypeID::VoidTyID;
        genPyCallFromInstruction(has_return, "call", i);
    }

    void visitUnreachableInst(const llvm::UnreachableInst &i)
    {
        genPyCallFromInstruction(false, "unreachable", i);
    }

    void visitInstruction(const llvm::Instruction &i)
    {
#if !defined(NDEBUG) || defined(LLVM_ENABLE_DUMP)
        i.dump();
#endif
        llvm::report_fatal_error("Unhandled instruction class");
    }

    void visit(llvm::Instruction &i)
    {
        if (llvm::dyn_cast<llvm::DbgDeclareInst>(&i) || llvm::dyn_cast<llvm::DbgValueInst>(&i) ||
            llvm::dyn_cast<llvm::DbgInfoIntrinsic>(&i)) {
            return;
        }

        const auto dbg = print(&i.getDebugLoc());
        if (!dbg.empty()) {
            emitter_.line(genPyCall("debug_loc", {quote(name(&i)), quote(dbg)}, {}));
        }

        llvm::InstVisitor<PyInstVisitor>::visit(i);

    }
};

void PyLLVMEmitter::emitBasicBlock(llvm::BasicBlock &bb)
{
    this->genDef("bb_" + getPrintingName(bb, true, *module_), {"pred"},
                   [&]() {
                       PyInstVisitor pv{*this, *module_};
                       for (auto &instr : bb.getInstList()) {
                           pv.visit(instr);
                       }
                   });
}

void PyLLVMEmitter::emitFunction(llvm::Function &function)
{
    if (function.isDeclaration()) {
        return;
    }

    std::vector<std::string> arglist = {"ctx"};

    for (unsigned long i = 0; i < function.arg_size(); ++i) {
        arglist.push_back("arg" + std::to_string(arglist.size()));
    }

    const std::string function_name = getPrintingName(function, true, *module_);

    this->genDef("func_" + function_name, arglist, [&]() {
        this->line("irpy = ctx['eval']");
        this->line("ctx['stacktrace'][-1] = {'function':" + quote(function_name) + "}");

        int i = 0;
        for (auto &arg : function.args()) {
            this->line("assert itypes.has_type(ctx, " + arglist[i + 1] + ", " + nameType(&arg) +
                         ")" + ", 'Incorrect BitVec size'");
            this->line("ctx.stack[\"" + (getPrintingName(arg, false, *module_)) + "\"] = " +
                         arglist[i + 1]);
            ++i;
        }

        for (auto &bb : function.getBasicBlockList()) {
            this->emitBasicBlock(bb);
        }

        this->line("return bb_" + getPrintingName(function.getEntryBlock(), true, *module_) +
                     "(None)");
    });
}

void PyLLVMEmitter::emitMetadata(void)
{
    MetadataVisitor mv{*module_};
    mv.visit(*module_);
    for (const auto &meta : mv.getMetadata()) {
        this->line("irpy.declare_metadata(ctx, " + quote("!" + std::to_string(meta.first)) + "," +
                     quote(meta.second) + ")");
    }
}

void PyLLVMEmitter::emitStructType(const llvm::StructType &type)
{
    std::string res;
    llvm::raw_string_ostream stream{res};
    stream << "itypes.declare_struct_type(ctx,";
    stream << quote(type.getName()) << ",";
    for (const auto &element : type.elements()) {
        stream << "'";
        element->print(stream, false);
        stream << "',";
    }
    stream << ")";
    this->line(stream.str());
}

void PyLLVMEmitter::emitGlobalVariable(const llvm::GlobalVariable &global)
{
    std::string res;
    llvm::raw_string_ostream stream{res};
    if (global.isConstant()) {
        stream << "irpy.declare_global_constant(ctx,";
    } else {
        stream << "irpy.declare_global_variable(ctx,";
    }
    stream << quote(getPrintingName(global, false, *module_)) << "," << nameType(&global) << ",";

    PyInstVisitor pv{*this, *module_};
    if (global.hasInitializer()) {
        stream << pv.visitConstant(global.getInitializer());
        stream << "," << nameType(global.getInitializer());
    }
    stream << ")";
    this->line(stream.str());
}

void PyLLVMEmitter::emitModule(void)
{
    this->line("import libirpy.itypes as itypes");
    this->line();

    this->genDef("_init_types", {"ctx"},
                   [&]() {
                       this->line("irpy = ctx['eval']");
                       for (const auto &type : module_->getIdentifiedStructTypes())
                           this->emitStructType(*type);
                   });

    this->line();

    this->genDef("_init_globals", {"ctx"},
                   [&]() {
                       this->line("irpy = ctx['eval']");
                       for (const auto &global : module_->getGlobalList())
                           this->emitGlobalVariable(global);
                   });

    this->line();

    for (auto &function : module_->getFunctionList()) {
        this->emitFunction(function);
    }

    this->genDef("_init_metadata", {"ctx"},
                   [&]() {
                       this->line("irpy = ctx['eval']");
                       this->emitMetadata();
                   });
}

} // namespace irpy
