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

import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.classes.JMethod;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        // 什么都不做！！！
        return out.copyFrom(in);
    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return cp.transferNode(stmt, in, out);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out;
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        var fact = out.copy();
        var op = edge.getSource().getDef();
        if (op.isPresent() && op.get() instanceof Var l && ConstantPropagation.canHoldInt(l)) {
            fact.remove(l);
        }
        return fact;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        assert edge.getSource() instanceof Invoke;

        var fact = new CPFact();
        var s = ((Invoke) edge.getSource()).getRValue().getArgs();
        var t = edge.getCallee().getIR().getParams();
        assert s.size() == t.size();

        for (int i = 0; i < s.size(); i++) {
            fact.update(t.get(i), callSiteOut.get(s.get(i)));
        }
        return fact;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        var fact = new CPFact();
        var op = edge.getCallSite().getDef();
        if (op.isEmpty() || !(op.get() instanceof Var l) || !ConstantPropagation.canHoldInt(l)) {
            return fact;
        }

        var v = Value.getUndef();
        for (var t : edge.getReturnVars()) {
            v = cp.meetValue(v, returnOut.get(t));
        }
        fact.update(l, v);
        return fact;
    }
}
