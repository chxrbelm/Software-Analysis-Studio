//===- Assignment-4.cpp -- Automated assertion-based verification (Static symbolic execution) --//
//
//                     SVF: Static Value-Flow Analysis
//
// Copyright (C) <2013-2022>  <Yulei Sui>
//

// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU Affero General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.

// This program is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU Affero General Public License for more details.

// You should have received a copy of the GNU Affero General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//
//===----------------------------------------------------------------------===//
/*
 * Automated assertion-based verification (Static symbolic execution)
 *
 * Created on: Feb 19, 2024
 */

#include "Assignment-4.h"

// SVF core headers
#include "SVFIR/SVFIR.h"
#include "SVFIR/SVFStmt.h"
#include "SVFIR/SVFValue.h"
#include "SVFIR/ICFG.h" 


// SVF utility headers
#include "Util/BasicTypes.h"
#include "Util/Options.h"

// Z3 manager
#include "Z3SSEMgr.h"

#include <cassert>
#include <iostream>
#include <sstream>

using namespace SVF;
using namespace SVFUtil;
using namespace llvm;
using namespace z3;


/// TODO: Implement your context-sensitive ICFG traversal here to traverse each program path (once for any loop) from
/// You will need to collect each path from src node to snk node and then add the path to the `paths` set by
/// calling the `collectAndTranslatePath` method which is then trigger the path translation.
/// This implementation, slightly different from Assignment-1, requires ICFGNode* as the first argument.
void SSE::reachability(const ICFGEdge *curEdge, const ICFGNode *sink) {

    // Push current edge to the working path
    path.push_back(curEdge);

    const ICFGNode *dstNode = curEdge->getDstNode();

    // --- Base case: reached sink node (assert call)
    if (dstNode == sink) {
        collectAndTranslatePath();
        path.pop_back();
        return;
    }

    // --- Context-sensitive visited check
    ICFGEdgeStackPair visitKey = std::make_pair(curEdge, callstack);
    if (visited.find(visitKey) != visited.end()) {
        path.pop_back();
        return; // already explored under this call context
    }
    visited.insert(visitKey);

    // --- Explore outgoing edges from the destination node
    for (const ICFGEdge *succEdge : dstNode->getOutEdges()) {

        if (!succEdge)
            continue;

        // Case 1: Call edge → push its call site to callstack
        if (const auto *callEdge = SVFUtil::dyn_cast<CallCFGEdge>(succEdge)) {
            const ICFGNode *calleeEntry = callEdge->getDstNode();
            callstack.push_back(calleeEntry);
            reachability(callEdge, sink);
            callstack.pop_back();
        }

        // Case 2: Return edge → pop matching call site if stack nonempty
        else if (const auto *retEdge = SVFUtil::dyn_cast<RetCFGEdge>(succEdge)) {
            if (!callstack.empty()) {
                const ICFGNode *lastCall = callstack.back();
                callstack.pop_back();
                reachability(retEdge, sink);
                callstack.push_back(lastCall);
            } else {
                reachability(retEdge, sink);
            }
        }

        // Case 3: Normal intra-procedural edge
        else if (const auto *intraEdge = SVFUtil::dyn_cast<IntraCFGEdge>(succEdge)) {
            reachability(intraEdge, sink);
        }
    }

    // --- Backtrack
    path.pop_back();
}

/// TODO: collect each path once this method is called during reachability analysis, and
/// Collect each program path from the entry to each assertion of the program. In this function,
/// you will need (1) add each path into the paths set, (2) call translatePath to convert each path into Z3 expressions.
/// Note that translatePath returns true if the path is feasible, false if the path is infeasible. (3) If a path is feasible,
/// you will need to call assertchecking to verify the assertion (which is the last ICFGNode of this path).
/// Collect and translate each feasible program path found by reachability()
void SSE::collectAndTranslatePath() {
    if (path.empty())
        return;

    // 1️⃣ Build a printable representation of the path for debugging and uniqueness
    std::stringstream ss;
    ss << "Path: ";
    for (const ICFGEdge *edge : path) {
        ss << edge->getSrcNode()->getId() << "->" << edge->getDstNode()->getId() << " ";
    }
    std::string pathStr = ss.str();

    // 2️⃣ Insert into the set to record this path (ensures uniqueness)
    paths.insert(pathStr);

    // 3️⃣ Translate this path into Z3 constraints
    bool feasible = translatePath(path);

    // 4️⃣ If path is feasible, verify the assertion at the last node
    if (feasible) {
        const ICFGEdge *lastEdge = path.back();
        const ICFGNode *lastNode = lastEdge->getDstNode();
        assertchecking(lastNode);
    }

    // Reset solver for the next path analysis
    resetSolver();
}


/// TODO: Implement handling of function calls
/// Handle function call: push solver context and bind actual to formal parameters
void SSE::handleCall(const CallCFGEdge* callEdge) {
    const ICFGNode* srcNode = callEdge->getSrcNode();
    DBOP(std::cout << "\n## Analyzing " << srcNode->toString() << "\n");

    const CallICFGNode* callNode   = SVFUtil::cast<CallICFGNode>(callEdge->getSrcNode());
    const FunEntryICFGNode* entry  = SVFUtil::cast<FunEntryICFGNode>(callEdge->getDstNode());

    // --- Save solver context before entering callee
    getSolver().push();

    // --- Bind each actual argument to its formal parameter (robust for all SVF versions)
    for (const SVFStmt* s : callNode->getSVFStmts()) {
        if (const auto* pe = SVFUtil::dyn_cast<CallPE>(s)) {
            NodeID lhs = pe->getLHSVarID();  // formal parameter
            NodeID rhs = pe->getRHSVarID();  // actual argument
            z3::expr lhsExpr = getZ3Expr(lhs);
            z3::expr rhsExpr = getZ3Expr(rhs);
            addToSolver(lhsExpr == rhsExpr);
        }
    }

    // --- Track the calling context (callee entry)
    pushCallingCtx(entry);

    DBOP(std::cout << "Entered function: " << entry->toString() << "\n");
}



/// TODO: Implement handling of function returns
/// Handle function return: pop solver context and bind return value back to caller
void SSE::handleRet(const RetCFGEdge* retEdge) {
    DBOP(std::cout << "\n## Analyzing " << retEdge->getDstNode()->toString() << "\n");

    const FunExitICFGNode* funExitNode = SVFUtil::cast<FunExitICFGNode>(retEdge->getSrcNode());
    const RetICFGNode* retNode = SVFUtil::cast<RetICFGNode>(retEdge->getDstNode());

    assert(retNode->getSVFStmts().size() <= 1 && "We can only have one RetPE per function!");

    // --- Locate RetPE safely across all SVF versions
    const RetPE* retPE = nullptr;
    for (const SVFStmt* s : retNode->getSVFStmts()) {
        if (const auto* r = SVFUtil::dyn_cast<RetPE>(s)) {
            retPE = r;
            break;
        }
    }

    // --- Capture RHS (return value) before popping solver context
    z3::expr rhs = getCtx().int_val(0);
    if (retPE) {
        rhs = getZ3Expr(retPE->getRHSVarID());
    }

    // --- Restore solver and calling context
    getSolver().pop();
    popCallingCtx();

    // --- Propagate return value back to caller if it exists
    if (retPE) {
        z3::expr lhs = getZ3Expr(retPE->getLHSVarID());
        addToSolver(lhs == rhs);
    }

    DBOP(std::cout << "Returned from function: " << funExitNode->toString() << "\n");
}



/// TODO: Implement handling of branch statements inside a function
/// Return true if the path is feasible, false otherwise.
/// A given branch on the ICFG looks like the following:
///       	     ICFGNode1 (condition %cmp)
///       	     1	/    \  0
///       	  ICFGNode2   ICFGNode3
/// edge->getCondition() returns the branch condition variable (%cmp) of type SVFValue* (for if/else) or a numeric condition variable (for switch).
/// Given the condition variable, you could obtain the SVFVar ID via "edge->getCondition())->getId()"
/// edge->getCondition() returns nullptr if this IntraCFGEdge is not a branch.
/// edge->getSuccessorCondValue() returns the actual condition value (1/0 for if/else) when this branch/IntraCFGEdge is executed. For example, the successorCondValue is 1 on the edge from ICFGNode1 to ICFGNode2, and 0 on the edge from ICFGNode1 to ICFGNode3
/// Handle branch statements inside a function.
/// Return true if the branch is feasible; false if infeasible.
bool SSE::handleBranch(const IntraCFGEdge* edge) {
    assert(edge->getCondition() && "not a conditional control-flow transfer?");
    
    z3::expr cond = getZ3Expr(edge->getCondition()->getId());
    z3::expr successorVal = getCtx().int_val(static_cast<int>(edge->getSuccessorCondValue()));

    DBOP(std::cout << "@@ Analyzing Branch " << edge->toString() << "\n");

    // Evaluate current symbolic condition
    z3::expr evalRes = getEvalExpr(cond == successorVal);

    // If Z3 proves condition cannot hold → infeasible path
    if (evalRes.is_false()) {
        addToSolver(cond != successorVal);
        DBOP(std::cout << "Infeasible branch detected: " 
                       << edge->toString() << " (cond != successor)\n");
        return false;
    }
    // If Z3 proves condition must hold → feasible branch
    else if (evalRes.is_true()) {
        addToSolver(cond == successorVal);
        DBOP(std::cout << "Feasible branch (cond == successor)\n");
        return true;
    }
    // Unknown / symbolic → treat as feasible and explore both
    else {
        addToSolver(cond == successorVal);
        DBOP(std::cout << "Symbolically feasible branch (unknown -> exploring)\n");
        return true;
    }
}


/// TODO: Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt and CmpStmt
/// Translate AddrStmt, CopyStmt, LoadStmt, StoreStmt, GepStmt, BinaryOPStmt, CmpStmt, SelectStmt, and PhiStmt
bool SSE::handleNonBranch(const IntraCFGEdge* edge) {
    const ICFGNode* dstNode = edge->getDstNode();
    const ICFGNode* srcNode = edge->getSrcNode();
    DBOP(if(!SVFUtil::isa<CallICFGNode>(dstNode) && !SVFUtil::isa<RetICFGNode>(dstNode)) std::cout << "\n## Analyzing "<< dstNode->toString() << "\n");

    for (const SVFStmt *stmt : dstNode->getSVFStmts())
    {
        if (const AddrStmt *addr = SVFUtil::dyn_cast<AddrStmt>(stmt))
        {
            // LHS := &RHS  (address of object)
            z3::expr lhs = getZ3Expr(addr->getLHSVarID());                 // :contentReference[oaicite:0]{index=0}
            z3::expr rhsAddr = getMemObjAddress(addr->getRHSVarID());       // :contentReference[oaicite:1]{index=1}
            addToSolver(lhs == rhsAddr);                                    // :contentReference[oaicite:2]{index=2}
        }
        else if (const CopyStmt *copy = SVFUtil::dyn_cast<CopyStmt>(stmt))
        {
            // LHS := RHS
            z3::expr lhs = getZ3Expr(copy->getLHSVarID());                  // :contentReference[oaicite:3]{index=3}
            z3::expr rhs = getZ3Expr(copy->getRHSVarID());                  // :contentReference[oaicite:4]{index=4}
            addToSolver(lhs == rhs);
        }
        else if (const LoadStmt *load = SVFUtil::dyn_cast<LoadStmt>(stmt))
        {
            // LHS := *RHS
            z3::expr lhs = getZ3Expr(load->getLHSVarID());                  // :contentReference[oaicite:5]{index=5}
            z3::expr ptr = getZ3Expr(load->getRHSVarID());                  // :contentReference[oaicite:6]{index=6}
            z3::expr val = z3Mgr->loadValue(ptr);                           // :contentReference[oaicite:7]{index=7}/:contentReference[oaicite:8]{index=8}
            addToSolver(lhs == val);
        }
        else if (const StoreStmt *store = SVFUtil::dyn_cast<StoreStmt>(stmt))
        {
            // *LHS := RHS
            z3::expr ptr = getZ3Expr(store->getLHSVarID());                 // :contentReference[oaicite:9]{index=9}
            z3::expr val = getZ3Expr(store->getRHSVarID());                 // :contentReference[oaicite:10]{index=10}
            (void) z3Mgr->storeValue(ptr, val);                              // :contentReference[oaicite:11]{index=11}/:contentReference[oaicite:12]{index=12}
        }
        else if (const GepStmt *gep = SVFUtil::dyn_cast<GepStmt>(stmt))
        {
            // LHS := GEP(RHS, offset)
            z3::expr lhs = getZ3Expr(gep->getLHSVarID());                   // :contentReference[oaicite:13]{index=13}
            z3::expr basePtr = getZ3Expr(gep->getRHSVarID());               // :contentReference[oaicite:14]{index=14}
            s32_t offset = z3Mgr->getGepOffset(gep, callingCtx);            // :contentReference[oaicite:15]{index=15}/:contentReference[oaicite:16]{index=16}
            z3::expr gepAddr = z3Mgr->getGepObjAddress(basePtr, offset);    // :contentReference[oaicite:17]{index=17}/:contentReference[oaicite:18]{index=18}
            addToSolver(lhs == gepAddr);
        }
        // Cmp: r = (a ? b), r is 0/1
        else if (const CmpStmt *cmp = SVFUtil::dyn_cast<CmpStmt>(stmt))
        {
            z3::expr op0 = getZ3Expr(cmp->getOpVarID(0));                    // :contentReference[oaicite:19]{index=19}
            z3::expr op1 = getZ3Expr(cmp->getOpVarID(1));                    // :contentReference[oaicite:20]{index=20}
            z3::expr res = getZ3Expr(cmp->getResID());                       // :contentReference[oaicite:21]{index=21}
            z3::expr one  = getCtx().int_val(1);                             // :contentReference[oaicite:22]{index=22}
            z3::expr zero = getCtx().int_val(0);                             // :contentReference[oaicite:23]{index=23}

            switch (cmp->getPredicate()) {
                case CmpStmt::ICMP_EQ:  addToSolver(res == ite(op0 == op1, one, zero)); break;
                case CmpStmt::ICMP_NE:  addToSolver(res == ite(op0 != op1, one, zero)); break;
                // Unsigned comparisons use the same integer domain here
                case CmpStmt::ICMP_UGT: addToSolver(res == ite(op0 >  op1, one, zero)); break;
                case CmpStmt::ICMP_UGE: addToSolver(res == ite(op0 >= op1, one, zero)); break;
                case CmpStmt::ICMP_ULT: addToSolver(res == ite(op0 <  op1, one, zero)); break;
                case CmpStmt::ICMP_ULE: addToSolver(res == ite(op0 <= op1, one, zero)); break;
                // Signed comparisons (same int semantics in this model)
                case CmpStmt::ICMP_SGT: addToSolver(res == ite(op0 >  op1, one, zero)); break;
                case CmpStmt::ICMP_SGE: addToSolver(res == ite(op0 >= op1, one, zero)); break;
                case CmpStmt::ICMP_SLT: addToSolver(res == ite(op0 <  op1, one, zero)); break;
                case CmpStmt::ICMP_SLE: addToSolver(res == ite(op0 <= op1, one, zero)); break;
                default:
                    assert(false && "unhandled integer Cmp predicate");
            }
        }
        else if (const BinaryOPStmt *binary = SVFUtil::dyn_cast<BinaryOPStmt>(stmt))
        {
            z3::expr op0 = getZ3Expr(binary->getOpVarID(0));
            z3::expr op1 = getZ3Expr(binary->getOpVarID(1));
            z3::expr res = getZ3Expr(binary->getResID());
            switch (binary->getOpcode())
            {
            case BinaryOperator::Add:
                addToSolver(res == op0 + op1);
                break;
            case BinaryOperator::Sub:
                addToSolver(res == op0 - op1);
                break;
            case BinaryOperator::Mul:
                addToSolver(res == op0 * op1);
                break;
            case BinaryOperator::SDiv:
                addToSolver(res == op0 / op1);
                break;
            case BinaryOperator::SRem:
                addToSolver(res == op0 % op1);
                break;
            case BinaryOperator::Xor:
                addToSolver(res == bv2int(int2bv(32, op0) ^ int2bv(32, op1), 1));
                break;
            case BinaryOperator::And:
                addToSolver(res == bv2int(int2bv(32, op0) & int2bv(32, op1), 1));
                break;
            case BinaryOperator::Or:
                addToSolver(res == bv2int(int2bv(32, op0) | int2bv(32, op1), 1));
                break;
            case BinaryOperator::AShr:
                addToSolver(res == bv2int(ashr(int2bv(32, op0), int2bv(32, op1)), 1));
                break;
            case BinaryOperator::Shl:
                addToSolver(res == bv2int(shl(int2bv(32, op0), int2bv(32, op1)), 1));
                break;
            default:
                assert(false && "implement this part");
            }
        }
        else if (const BranchStmt *br = SVFUtil::dyn_cast<BranchStmt>(stmt))
        {
            DBOP(std::cout << "\t skip handled when traversal Conditional IntraCFGEdge \n");
        }
        else if (const SelectStmt *select = SVFUtil::dyn_cast<SelectStmt>(stmt)) {
            z3::expr res = getZ3Expr(select->getResID());
            z3::expr tval = getZ3Expr(select->getTrueValue()->getId());
            z3::expr fval = getZ3Expr(select->getFalseValue()->getId());
            z3::expr cond = getZ3Expr(select->getCondition()->getId());
            addToSolver(res == ite(cond == getCtx().int_val(1), tval, fval));
        }
        else if (const PhiStmt *phi = SVFUtil::dyn_cast<PhiStmt>(stmt)) {
            z3::expr res = getZ3Expr(phi->getResID());
            bool opINodeFound = false;
            for(u32_t i = 0; i < phi->getOpVarNum(); i++){
                assert(srcNode && "we don't have a predecessor ICFGNode?");
                if (srcNode->getFun()->postDominate(srcNode->getBB(),phi->getOpICFGNode(i)->getBB()))
                {
                    z3::expr ope = getZ3Expr(phi->getOpVar(i)->getId());
                    addToSolver(res == ope);
                    opINodeFound = true;
                }
            }
            assert(opINodeFound && "predecessor ICFGNode of this PhiStmt not found?");
        }
    }

    return true;
}


/// Traverse each program path
bool SSE::translatePath(std::vector<const ICFGEdge*>& path) {
	for (const ICFGEdge* edge : path) {
		if (const IntraCFGEdge* intraEdge = SVFUtil::dyn_cast<IntraCFGEdge>(edge)) {
			if (handleIntra(intraEdge) == false)
				return false;
		}
		else if (const CallCFGEdge* call = SVFUtil::dyn_cast<CallCFGEdge>(edge)) {
			handleCall(call);
		}
		else if (const RetCFGEdge* ret = SVFUtil::dyn_cast<RetCFGEdge>(edge)) {
			handleRet(ret);
		}
		else
			assert(false && "what other edges we have?");
	}

	return true;
}

/// Program entry
void SSE::analyse() {
	for (const ICFGNode* src : identifySources()) {
		assert(SVFUtil::isa<GlobalICFGNode>(src) && "reachability should start with GlobalICFGNode!");
		for (const ICFGNode* sink : identifySinks()) {
			const IntraCFGEdge startEdge(nullptr, const_cast<ICFGNode*>(src));
			/// start traversing from the entry to each assertion and translate each path
			reachability(&startEdge, sink);
			resetSolver();
		}
	}
}
