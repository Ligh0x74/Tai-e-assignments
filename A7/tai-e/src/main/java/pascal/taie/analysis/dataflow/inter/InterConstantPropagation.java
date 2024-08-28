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

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.*;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.FieldRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;

import java.util.*;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private Map<JField, List<StoreField>> jFieldToStoreFieldsMap;

    private Map<Var, List<Var>> varToVarsMap;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        jFieldToStoreFieldsMap = new HashMap<>();
        varToVarsMap = new HashMap<>();
        // 获取所有的静态 store 语句，限制为 int 类型，设置 JField 到对应 store 语句的映射
        icfg.forEach(stmt -> {
            if (stmt instanceof StoreField storeField && storeField.isStatic() && ConstantPropagation.canHoldInt(storeField.getRValue())) {
                // TODO - can use JField as id or not?
                var jField = storeField.getFieldRef().resolve();
                jFieldToStoreFieldsMap.computeIfAbsent(jField, k -> new ArrayList<>()).add(storeField);
            }
        });
        // 计算别名信息
        pta.getVars().forEach(v1 -> {
            var pts1 = pta.getPointsToSet(v1);
            if (pts1.isEmpty()) {
                varToVarsMap.computeIfAbsent(v1, k -> new ArrayList<>()).add(v1);
                return;
            }
            pta.getVars().forEach(v2 -> {
                var pts2 = pta.getPointsToSet(v2);
                for (var o : pts2) {
                    if (pts1.contains(o)) {
                        varToVarsMap.computeIfAbsent(v1, k -> new ArrayList<>()).add(v2);
                        break;
                    }
                }
            });
        });
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
        // 处理 load 语句，限制为 int 类型
        if (stmt instanceof LoadField loadField && ConstantPropagation.canHoldInt(loadField.getLValue())) {
            // 静态字段
            if (loadField.isStatic()) {
                var jField = loadField.getFieldRef().resolve();
                var meetResult = Value.getUndef();
                if (!jFieldToStoreFieldsMap.containsKey(jField)) {
                    in = in.copy();
                    in.update(loadField.getLValue(), meetResult);
                    return out.copyFrom(in);
                }
                for (var storeField : jFieldToStoreFieldsMap.get(jField)) {
                    var storeFieldInFact = solver.getInFact(storeField);
                    if (storeFieldInFact == null) {
                        continue;
                    }
                    meetResult = cp.meetValue(meetResult, storeFieldInFact.get(storeField.getRValue()));
                }
                in = in.copy();
                in.update(loadField.getLValue(), meetResult);
                return out.copyFrom(in);
            }
            // 实例字段
            // 如何获取 loadField 中 x.f 的 x？InstanceFieldAccess！
            var instanceFieldAccess = (InstanceFieldAccess) loadField.getFieldAccess();
            var v = instanceFieldAccess.getBase();
            var meetResult = Value.getUndef();
            // null check
            if (!varToVarsMap.containsKey(v)) {
//                in = in.copy();
//                in.update(loadField.getLValue(), Value.getNAC());
                return out.copyFrom(in);
            }
            for (var alias : varToVarsMap.get(v)) {
                for (var storeField : alias.getStoreFields()) {
                    var storeFieldInFact = solver.getInFact(storeField);
                    if (storeFieldInFact == null) {
                        continue;
                    }
                    meetResult = cp.meetValue(meetResult, storeFieldInFact.get(storeField.getRValue()));
                }
            }
            in = in.copy();
            in.update(loadField.getLValue(), meetResult);
            return out.copyFrom(in);
        }
        if (stmt instanceof LoadArray loadArray && ConstantPropagation.canHoldInt(loadArray.getLValue())) {
            var base = loadArray.getArrayAccess().getBase();
            var index = in.get(loadArray.getArrayAccess().getIndex());
            var meetResult = Value.getUndef();
            // null check
            if (!varToVarsMap.containsKey(base)) {
//                in = in.copy();
//                in.update(loadArray.getLValue(), Value.getNAC());
                return out.copyFrom(in);
            }
            for (var mayAlias : varToVarsMap.get(base)) {
                for (var storeArray : mayAlias.getStoreArrays()) {
                    var storeArrayInFact = solver.getInFact(storeArray);
                    if (storeArrayInFact == null) {
                        continue;
                    }
                    var storeArrayIndex = storeArrayInFact.get(storeArray.getArrayAccess().getIndex());
                    if (index.isUndef() || storeArrayIndex.isUndef() || (index.isConstant()
                            && storeArrayIndex.isConstant()
                            && index.getConstant() != storeArrayIndex.getConstant()
                    )) {
                        continue;
                    }
                    meetResult = cp.meetValue(meetResult, storeArrayInFact.get(storeArray.getRValue()));
                }
            }
            in = in.copy();
            in.update(loadArray.getLValue(), meetResult);
            return out.copyFrom(in);
        }
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
