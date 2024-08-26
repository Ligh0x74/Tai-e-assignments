/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.*;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)) {
            method.getIR().getStmts().forEach(stmt -> {
                stmt.accept(stmtProcessor);
            });
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            var pointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var obj = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(pointer, obj);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var x = pointerFlowGraph.getVarPtr(stmt.getLValue());
            var y = pointerFlowGraph.getVarPtr(stmt.getRValue());
            addPFGEdge(y, x);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.getFieldRef().isStatic()) {
                var x = pointerFlowGraph.getVarPtr(stmt.getLValue());
                var y = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(y, x);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.getFieldRef().isStatic()) {
                var x = pointerFlowGraph.getStaticField(stmt.getFieldRef().resolve());
                var y = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(y, x);
            }
            return null;
        }

        @Override
        public Void visit(Invoke stmt) {
            if (!stmt.isStatic()) {
                return null;
            }
            var m = resolveCallee(null, stmt);
            // 在调用图中添加边，以及调用 addReachable 方法
            callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(stmt), stmt, m));
            addReachable(m);

            var p = m.getIR().getParams();
            var a = stmt.getInvokeExp().getArgs();
            assert p.size() == a.size();
            for (int i = 0; i < p.size(); i++) {
                var x = pointerFlowGraph.getVarPtr(p.get(i));
                var y = pointerFlowGraph.getVarPtr(a.get(i));
                addPFGEdge(y, x);
            }

            if (stmt.getLValue() != null) {
                m.getIR().getReturnVars().forEach(r -> {
                    var x = pointerFlowGraph.getVarPtr(stmt.getLValue());
                    var y = pointerFlowGraph.getVarPtr(r);
                    addPFGEdge(y, x);
                });
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if (pointerFlowGraph.addEdge(source, target) && !source.getPointsToSet().isEmpty()) {
            workList.addEntry(target, source.getPointsToSet());
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while (!workList.isEmpty()) {
            var entry = workList.pollEntry();
            var delta = propagate(entry.pointer(), entry.pointsToSet());
            if (!(entry.pointer() instanceof VarPtr varPtr)) {
                continue;
            }
            var v = varPtr.getVar();
            delta.forEach(o -> {
                v.getStoreFields().forEach(s -> {
                    var x = pointerFlowGraph.getInstanceField(o, s.getFieldRef().resolve());
                    var y = pointerFlowGraph.getVarPtr(s.getRValue());
                    addPFGEdge(y, x);
                });
                v.getLoadFields().forEach(s -> {
                    var x = pointerFlowGraph.getVarPtr(s.getLValue());
                    var y = pointerFlowGraph.getInstanceField(o, s.getFieldRef().resolve());
                    addPFGEdge(y, x);
                });
                v.getStoreArrays().forEach(s -> {
                    var x = pointerFlowGraph.getArrayIndex(o);
                    var y = pointerFlowGraph.getVarPtr(s.getRValue());
                    addPFGEdge(y, x);
                });
                v.getLoadArrays().forEach(s -> {
                    var x = pointerFlowGraph.getVarPtr(s.getLValue());
                    var y = pointerFlowGraph.getArrayIndex(o);
                    addPFGEdge(y, x);
                });
                processCall(v, o);
            });
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var delta = new PointsToSet();
        pointsToSet.forEach(obj -> {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        });

        if (pointsToSet.isEmpty()) {
            return delta;
        }
        pointerFlowGraph.getSuccsOf(pointer).forEach(s -> {
            workList.addEntry(s, delta);
        });
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for (var invoke : var.getInvokes()) {
            if (invoke.isStatic()) {
                continue;
            }
            var m = resolveCallee(recv, invoke);
            workList.addEntry(pointerFlowGraph.getVarPtr(m.getIR().getThis()), new PointsToSet(recv));
            if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, m))) {
                addReachable(m);
                var p = m.getIR().getParams();
                var a = invoke.getInvokeExp().getArgs();
                assert p.size() == a.size();
                for (int i = 0; i < p.size(); i++) {
                    var x = pointerFlowGraph.getVarPtr(p.get(i));
                    var y = pointerFlowGraph.getVarPtr(a.get(i));
                    addPFGEdge(y, x);
                }

                if (invoke.getLValue() != null) {
                    m.getIR().getReturnVars().forEach(r -> {
                        var x = pointerFlowGraph.getVarPtr(invoke.getLValue());
                        var y = pointerFlowGraph.getVarPtr(r);
                        addPFGEdge(y, x);
                    });
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}
