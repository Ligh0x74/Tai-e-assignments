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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Copy;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.LoadArray;
import pascal.taie.ir.stmt.LoadField;
import pascal.taie.ir.stmt.New;
import pascal.taie.ir.stmt.StmtVisitor;
import pascal.taie.ir.stmt.StoreArray;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        if (callGraph.addReachableMethod(csMethod)) {
            csMethod.getMethod().getIR().getStmts().forEach(stmt -> {
                stmt.accept(new StmtProcessor(csMethod));
            });
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            var pointer = csManager.getCSVar(context, stmt.getLValue());
            var obj = heapModel.getObj(stmt);
            var pt = PointsToSetFactory.make(csManager.getCSObj(contextSelector.selectHeapContext(csMethod, obj), obj));
            workList.addEntry(pointer, pt);
            return null;
        }

        @Override
        public Void visit(Copy stmt) {
            var x = csManager.getCSVar(context, stmt.getLValue());
            var y = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(y, x);
            return null;
        }

        @Override
        public Void visit(LoadField stmt) {
            if (stmt.getFieldRef().isStatic()) {
                var x = csManager.getCSVar(context, stmt.getLValue());
                var y = csManager.getStaticField(stmt.getFieldRef().resolve());
                addPFGEdge(y, x);
            }
            return null;
        }

        @Override
        public Void visit(StoreField stmt) {
            if (stmt.getFieldRef().isStatic()) {
                var x = csManager.getStaticField(stmt.getFieldRef().resolve());
                var y = csManager.getCSVar(context, stmt.getRValue());
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
            var ct = contextSelector.selectContext(csManager.getCSCallSite(context, stmt), m);
            callGraph.addEdge(new Edge<>(
                    CallGraphs.getCallKind(stmt),
                    csManager.getCSCallSite(context, stmt),
                    csManager.getCSMethod(ct, m)
            ));
            addReachable(csManager.getCSMethod(ct, m));

            var p = m.getIR().getParams();
            var a = stmt.getInvokeExp().getArgs();
            assert p.size() == a.size();
            for (int i = 0; i < p.size(); i++) {
                var x = csManager.getCSVar(ct, p.get(i));
                var y = csManager.getCSVar(context, a.get(i));
                addPFGEdge(y, x);
            }

            if (stmt.getLValue() != null) {
                m.getIR().getReturnVars().forEach(r -> {
                    var x = csManager.getCSVar(context, stmt.getLValue());
                    var y = csManager.getCSVar(ct, r);
                    addPFGEdge(y, x);
                });
            }

            if (stmt.getDef().isPresent()) {
                taintAnalysis.callSource(stmt, context);
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
            if (delta.isEmpty() || !(entry.pointer() instanceof CSVar csVar)) {
                continue;
            }
            var v = csVar.getVar();
            delta.forEach(o -> {
                var context = csVar.getContext();
                v.getStoreFields().forEach(s -> {
                    var x = csManager.getInstanceField(o, s.getFieldRef().resolve());
                    var y = csManager.getCSVar(context, s.getRValue());
                    addPFGEdge(y, x);
                });
                v.getLoadFields().forEach(s -> {
                    var x = csManager.getCSVar(context, s.getLValue());
                    var y = csManager.getInstanceField(o, s.getFieldRef().resolve());
                    addPFGEdge(y, x);
                });
                v.getStoreArrays().forEach(s -> {
                    var x = csManager.getArrayIndex(o);
                    var y = csManager.getCSVar(context, s.getRValue());
                    addPFGEdge(y, x);
                });
                v.getLoadArrays().forEach(s -> {
                    var x = csManager.getCSVar(context, s.getLValue());
                    var y = csManager.getArrayIndex(o);
                    addPFGEdge(y, x);
                });
                processCall(csVar, o);
            });

            callGraph.forEach(csMethod -> {
                csMethod.getEdges().forEach(edge -> {
                    var invoke = edge.getCallSite().getCallSite();
                    var context = edge.getCallSite().getContext();
                    if (!invoke.isStatic() && invoke.getDef().isPresent()) {
                        taintAnalysis.callBaseToResult(invoke, context);
                    }
                    if (!invoke.isStatic()) {
                        taintAnalysis.callArgToBase(invoke, context);
                    }
                    if (invoke.getDef().isPresent()) {
                        taintAnalysis.callArgToResult(invoke, context);
                    }
                });
            });
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        var delta = PointsToSetFactory.make();
        pointsToSet.forEach(obj -> {
            if (pointer.getPointsToSet().addObject(obj)) {
                delta.addObject(obj);
            }
        });
        if (!delta.isEmpty()) {
            pointerFlowGraph.getSuccsOf(pointer).forEach(s -> {
                workList.addEntry(s, delta);
            });
        }
        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        for (var invoke : recv.getVar().getInvokes()) {
            if (invoke.isStatic()) {
                continue;
            }
            var context = recv.getContext();
            var m = resolveCallee(recvObj, invoke);
            var ct = contextSelector.selectContext(csManager.getCSCallSite(context, invoke), recvObj, m);
            workList.addEntry(csManager.getCSVar(ct, m.getIR().getThis()), PointsToSetFactory.make(recvObj));
            if (callGraph.addEdge(new Edge<>(
                    CallGraphs.getCallKind(invoke),
                    csManager.getCSCallSite(context, invoke),
                    csManager.getCSMethod(ct, m)
            ))) {
                addReachable(csManager.getCSMethod(ct, m));
                var p = m.getIR().getParams();
                var a = invoke.getInvokeExp().getArgs();
                assert p.size() == a.size();
                for (int i = 0; i < p.size(); i++) {
                    var x = csManager.getCSVar(ct, p.get(i));
                    var y = csManager.getCSVar(context, a.get(i));
                    addPFGEdge(y, x);
                }

                if (invoke.getLValue() != null) {
                    m.getIR().getReturnVars().forEach(r -> {
                        var x = csManager.getCSVar(context, invoke.getLValue());
                        var y = csManager.getCSVar(ct, r);
                        addPFGEdge(y, x);
                    });
                }
            }

            if (invoke.getDef().isPresent()) {
                taintAnalysis.callSource(invoke, context);
            }
        }
    }

    public void addWorkList(Pointer pointer, PointsToSet pointsToSet) {
        workList.addEntry(pointer, pointsToSet);
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}
