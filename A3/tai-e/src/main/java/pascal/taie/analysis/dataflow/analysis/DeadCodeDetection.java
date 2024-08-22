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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.ArrayAccess;
import pascal.taie.ir.exp.CastExp;
import pascal.taie.ir.exp.FieldAccess;
import pascal.taie.ir.exp.NewExp;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.*;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode
        // BFS
        Set<Stmt> vis = new HashSet<>();
        Queue<Stmt> q = new ArrayDeque<>();
        q.offer(cfg.getEntry());
        while (!q.isEmpty()) {
            var stmt = q.poll();
            if (vis.contains(stmt)) {
                continue;
            }
            vis.add(stmt);
            var outEdges = cfg.getOutEdgesOf(stmt);
            // 不可达代码
            if (stmt instanceof If s) {
                var val = ConstantPropagation.evaluate(s.getCondition(), constants.getInFact(s));
                outEdges.forEach(edge -> {
                    boolean ok = !val.isConstant();
                    ok = ok || (val.getConstant() == 1 && edge.getKind() == Edge.Kind.IF_TRUE);
                    ok = ok || (val.getConstant() == 0 && edge.getKind() == Edge.Kind.IF_FALSE);
                    if (ok) {
                        q.offer(edge.getTarget());
                    }
                });
            } else if (stmt instanceof SwitchStmt s) {
                var val = constants.getInFact(s).get(s.getVar());
                if (!val.isConstant()) {
                    outEdges.forEach(edge -> q.offer(edge.getTarget()));
                    continue;
                }
                boolean isDefault = true;
                for (var edge : outEdges) {
                    boolean ok = edge.isSwitchCase() && val.getConstant() == edge.getCaseValue();
                    if (ok) {
                        isDefault = false;
                        q.offer(edge.getTarget());
                        break;
                    }
                }
                if (isDefault) {
                    q.offer(s.getDefaultTarget());
                }
            } else {
                cfg.getSuccsOf(stmt).forEach(q::offer);
            }
            // 无用赋值
            if(stmt instanceof AssignStmt s) {
                if (!hasNoSideEffect(s.getRValue())) {
                    continue;
                }
                if (s.getLValue() instanceof Var v && !liveVars.getOutFact(s).contains(v)) {
                    deadCode.add(s);
                }
            }
        }

        // deadLoop exclude exit node
        vis.add(cfg.getExit());
        cfg.forEach(stmt -> {
            if (!vis.contains(stmt)) {
                deadCode.add(stmt);
            }
        });
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}
