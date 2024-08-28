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

    private Map<JField, Set<StoreField>> jFieldToStoreFieldsMap;

    private Map<Var, Set<Var>> varAliasMap;

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        // 添加静态字段的 JField 到对应 Store 语句的映射，限制为 int 类型
        jFieldToStoreFieldsMap = new HashMap<>();
        icfg.forEach(stmt -> {
            if (stmt instanceof StoreField storeField && storeField.isStatic() && ConstantPropagation.canHoldInt(storeField.getRValue())) {
                var jField = storeField.getFieldAccess().getFieldRef().resolve();
                jFieldToStoreFieldsMap.computeIfAbsent(jField, k -> new HashSet<>()).add(storeField);
            }
        });
        // 添加变量到对应 pts 存在交集的变量的映射
        varAliasMap = new HashMap<>();
        pta.getVars().forEach(v1 -> {
            if (pta.getPointsToSet(v1).isEmpty()) {
                varAliasMap.computeIfAbsent(v1, k -> new HashSet<>()).add(v1);
                return;
            }
            pta.getVars().forEach(v2 -> {
                for (var obj : pta.getPointsToSet(v2)) {
                    if (pta.getPointsToSet(v1).contains(obj)) {
                        varAliasMap.computeIfAbsent(v1, k -> new HashSet<>()).add(v2);
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
        // 处理 Load 语句，限定为 int 类型
        if (stmt instanceof LoadField loadField && ConstantPropagation.canHoldInt(loadField.getLValue())) {
            if (loadField.isStatic()) {
                return transforStaticLoadFieleNodeLimitInt(loadField, in, out);
            }
            return transforInstanceLoadFieldNodeLimitInt(loadField, in, out);
        }
        if (stmt instanceof LoadArray loadArray && ConstantPropagation.canHoldInt(loadArray.getLValue())) {
            return transforLoadArrayNodeLimitInt(loadArray, in, out);
        }
        return cp.transferNode(stmt, in, out);
    }

    private boolean transforStaticLoadFieleNodeLimitInt(LoadField loadField, CPFact in, CPFact out) {
        var jField = loadField.getFieldRef().resolve();
        var meetResult = Value.getUndef();
        // TODO - 断言 jFild 在 jFieldToStoreFieldsMap 中
        assert jFieldToStoreFieldsMap.containsKey(jField);
        for (var storeField : jFieldToStoreFieldsMap.get(jField)) {
            var storeFieldInFact = solver.getInFact(storeField);
            assert storeFieldInFact != null;
            meetResult = cp.meetValue(meetResult, storeFieldInFact.get(storeField.getRValue()));
        }
        in = in.copy();
        in.update(loadField.getLValue(), meetResult);
        return out.copyFrom(in);
    }

    private boolean transforInstanceLoadFieldNodeLimitInt(LoadField loadField, CPFact in, CPFact out) {
        assert loadField.getFieldAccess() instanceof InstanceFieldAccess;
        var base = ((InstanceFieldAccess) loadField.getFieldAccess()).getBase();
        var jField = loadField.getFieldRef().resolve();
        var meetResult = Value.getUndef();
        // TODO - 变量不在 PFG 中，如何处理？LoadField 的 Base 没有指向任何对象，说明无法处理 Base 的 Assign 语句，
        //  为了保证 Sound，应该将变量设置为 NAC？为什么不设置 NAC，而是直接返回。
        if (!varAliasMap.containsKey(base)) {
//            in = in.copy();
//            in.update(loadField.getLValue(), Value.getNAC());
            return out.copyFrom(in);
        }
        for (var alias : varAliasMap.get(base)) {
            for (var storeField : alias.getStoreFields()) {
                var storeFieldInFact = solver.getInFact(storeField);
                assert storeFieldInFact != null;
                // TODO - 我是傻逼，忘记判断字段是否相同，Bug 找好久才找到！
                if (!jField.equals(storeField.getFieldRef().resolve())) {
                    continue;
                }
                meetResult = cp.meetValue(meetResult, storeFieldInFact.get(storeField.getRValue()));
            }
        }
        in = in.copy();
        in.update(loadField.getLValue(), meetResult);
        return out.copyFrom(in);
    }

    private boolean transforLoadArrayNodeLimitInt(LoadArray loadArray, CPFact in, CPFact out) {
        var base = loadArray.getArrayAccess().getBase();
        var index = in.get(loadArray.getArrayAccess().getIndex());
        var meetResult = Value.getUndef();
        // TODO - 变量不在 PFG 中，如何处理？LoadField 的 Base 没有指向任何对象，说明无法处理 Base 的 Assign 语句，
        //  为了保证 Sound，应该将变量设置为 NAC？为什么不设置 NAC，而是直接返回。
        if (!varAliasMap.containsKey(base)) {
//            in = in.copy();
//            in.update(loadArray.getLValue(), Value.getNAC());
            return out.copyFrom(in);
        }
        for (var alias : varAliasMap.get(base)) {
            for (var storeArray : alias.getStoreArrays()) {
                var storeFieldInFact = solver.getInFact(storeArray);
                assert storeFieldInFact != null;
                // 比较索引
                var storeIndex = storeFieldInFact.get(storeArray.getArrayAccess().getIndex());
                if (index.isUndef() || storeIndex.isUndef() || (index.isConstant() && storeIndex.isConstant() && index.getConstant() != storeIndex.getConstant())) {
                    continue;
                }
                meetResult = cp.meetValue(meetResult, storeFieldInFact.get(storeArray.getRValue()));
            }
        }
        in = in.copy();
        in.update(loadArray.getLValue(), meetResult);
        return out.copyFrom(in);
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
