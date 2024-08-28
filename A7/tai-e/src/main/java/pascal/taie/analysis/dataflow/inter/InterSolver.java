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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.StoreField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.SetQueue;

import java.util.ArrayDeque;
import java.util.Queue;
import java.util.Set;
import java.util.stream.Collectors;

/**
 * Solver for inter-procedural data-flow analysis.
 * The workload of inter-procedural analysis is heavy, thus we always
 * adopt work-list algorithm for efficiency.
 */
class InterSolver<Method, Node, Fact> {

    private final InterDataflowAnalysis<Node, Fact> analysis;

    private final ICFG<Method, Node> icfg;

    private DataflowResult<Node, Fact> result;

    private Queue<Node> workList;

    InterSolver(InterDataflowAnalysis<Node, Fact> analysis,
                ICFG<Method, Node> icfg) {
        this.analysis = analysis;
        this.icfg = icfg;
    }

    DataflowResult<Node, Fact> solve() {
        result = new DataflowResult<>();
        initialize();
        doSolve();
        return result;
    }

    private void initialize() {
        // TODO - finish me
        icfg.entryMethods().forEach(m -> {
            // entry method's entry
            var node = icfg.getEntryOf(m);
            result.setOutFact(node, analysis.newBoundaryFact(node));
        });
        for (var node : icfg) {
            if (result.getOutFact(node) != null) {
                continue;
            }
            result.setOutFact(node, analysis.newInitialFact());
        }
    }

    private void doSolve() {
        // TODO - finish me
//        Queue<Node> q = new ArrayDeque<>();
//        icfg.forEach(q::offer);
//        while (!q.isEmpty()) {
//            var node = q.poll();
//            var inFact = analysis.newInitialFact();
//            for (var edge : icfg.getInEdgesOf(node)) {
//                var pred = analysis.transferEdge(edge, result.getOutFact(edge.getSource()));
//                analysis.meetInto(pred, inFact);
//            }
//            result.setInFact(node, inFact);
//            if (analysis.transferNode(node, inFact, result.getOutFact(node))) {
//                icfg.getSuccsOf(node).forEach(q::offer);
//            }
//        }

        boolean changed = true;
        while (changed) {
            changed = false;
            for (var node : icfg) {
                var inFact = analysis.newInitialFact();
                for (var edge : icfg.getInEdgesOf(node)) {
                    var pred = analysis.transferEdge(edge, result.getOutFact(edge.getSource()));
                    analysis.meetInto(pred, inFact);
                }
                result.setInFact(node, inFact);
                changed |= analysis.transferNode(node, inFact, result.getOutFact(node));
            }
        }
    }

    public Fact getInFact(Node node) {
        return result.getInFact(node);
    }
}
