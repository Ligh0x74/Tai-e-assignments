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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.context.ListContext;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.InvokeStatic;
import pascal.taie.ir.stmt.Invoke;

import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    /**
     * 返回一个集合，其中包含污点分析检测到的所有 taint flows。提示：你可以在这个方法中实现处理 sink 的规则（在第 2.1 节给出过）。
     * <p>
     * 在 TaintAnalysiss 的构造函数中，我们已经给出了解析配置文件的代码，并把解析的结果保存在了 config 字段中，你可以直接使用它。此外，我们也初始化了 TaintManager 对象并将其保存在了 manager 字段中，你可以通过它来管理污点对象。如果你的实现还需要做一些初始化工作，你也可以在构造函数中添加你的代码。
     * <p>
     * 在这次作业中，指针分析和污点分析互相依赖，所以 Solver 和 TaintAnalysiss 各自保存了指向对方的引用，即 Solver 中的 taintAnalysis 字段和 TaintAnalysiss 中的 solver 字段。你需要想清楚如何利用这两个引用字段实现两个分析之间的交互。如果有需要的话，你也可以向这两个类中添加自己需要的字段和方法。
     */
    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.
        var sinks = config.getSinks();
        result.getCSCallGraph().forEach(csMethod -> {
            // 如果方法的第 i 个参数是 Sink，遍历它的每个调用点，将第 i 实参的 pts 指向的每个污点对象加入 TaintFlows 中
            var method = csMethod.getMethod();
            for (int i = 0; i < method.getParamCount(); i++) {
                if (!sinks.contains(new Sink(method, i))) {
                    continue;
                }
                for (var edge : csMethod.getEdges()) {
                    var csCallSite = edge.getCallSite();
                    var context = csCallSite.getContext();
                    var callSite = csCallSite.getCallSite();
                    var arg = callSite.getInvokeExp().getArgs().get(i);
                    for (var csObj : csManager.getCSVar(context, arg).getPointsToSet()) {
                        if (manager.isTaint(csObj.getObject())) {
                            taintFlows.add(new TaintFlow(manager.getSourceCall(csObj.getObject()), callSite, i));
                        }
                    }
                }
            }
        });
        return taintFlows;
    }

    public void callSource(Invoke invoke, Context context) {
        // 获取 Sources
        var sources = config.getSources();
        // 如果 <m, u> 在 Sources 中，则将 <r, {t}> 加入到 WorkList 中
        var m = invoke.getMethodRef().resolve();
        var u = invoke.getMethodRef().getReturnType();
        if (sources.contains(new Source(m, u))) {
            var t = csManager.getCSObj(emptyContext, manager.makeTaint(invoke, u));
            var r = csManager.getCSVar(context, invoke.getLValue());
            solver.addWorkList(r, PointsToSetFactory.make(t));
        }
    }

    /**
     * 注意，因为静态方法没有 base 变量，所以他们不会引起 base-to-result 和 arg-to-base 的污点传播。此外，一些方法可能会引起多种污点传播，例如 String.concat(String) 不仅会引发 arg-to-result 的传播，也会引发 base-to-result 的传播。这是因为，它的返回值中同时包含了参数和 receiver object 的内容。
     * <p>
     * base-to-result，在 PFG 中没有 base 到 result 的边，所以当 taint object 传播到变量 x 时，手动对该变量的所有 Invoke 语句调用当前方法。arg-to-result 和 arg-to-base，则对 CallGraph 所有 Invoke 调用相应方法，因为无法获取 arg 对应的 Invoke。（或者可以创建一个映射关系）
     */
    public void callBaseToResult(Invoke invoke, Context context) {
        // 获取 TaintTransfers
        var transfers = config.getTransfers();
        // 如果 <m, base, result, u> 在 TaintTransfers 中，对于 Base 变量指向的污点对象集合 c，将 <r, c> 加入到 WorkList 中
        var m = invoke.getMethodRef().resolve();
        var u = invoke.getMethodRef().getReturnType();
        if (!transfers.contains(new TaintTransfer(m, TaintTransfer.BASE, TaintTransfer.RESULT, u))) {
            return;
        }
        assert !invoke.isStatic();
        var base = ((InvokeInstanceExp) invoke.getInvokeExp()).getBase();
        var x = csManager.getCSVar(context, base);
        var r = csManager.getCSVar(context, invoke.getLValue());
        var pointsToSet = PointsToSetFactory.make();
        x.getPointsToSet().forEach(csObj -> {
            if (manager.isTaint(csObj.getObject())) {
                // 新污点对象的 source call 和原污点对象相同
                var t = csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(csObj.getObject()), u));
                pointsToSet.addObject(t);
            }
        });
        if (!pointsToSet.isEmpty()) {
            solver.addWorkList(r, pointsToSet);
        }
    }

    public void callArgToResult(Invoke invoke, Context context) {
        // 获取 TaintTransfers
        var transfers = config.getTransfers();
        // 如果 <m, i, result, u> 在 TaintTransfers 中，对于第 i 个实参指向的污点对象集合 c，将 <r, c> 加入到 WorkList 中
        var m = invoke.getMethodRef().resolve();
        var u = invoke.getMethodRef().getReturnType();
        var r = csManager.getCSVar(context, invoke.getLValue());
        var pointsToSet = PointsToSetFactory.make();
        for (int i = 0; i < m.getParamCount(); i++) {
            if (!transfers.contains(new TaintTransfer(m, i, TaintTransfer.RESULT, u))) {
                continue;
            }
            var arg = invoke.getInvokeExp().getArgs().get(i);
            for (var csObj : csManager.getCSVar(context, arg).getPointsToSet()) {
                if (manager.isTaint(csObj.getObject())) {
                    // 新污点对象的 source call 和原污点对象相同
                    var t = csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(csObj.getObject()), u));
                    pointsToSet.addObject(t);
                }
            }
        }
        if (!pointsToSet.isEmpty()) {
            solver.addWorkList(r, pointsToSet);
        }
    }

    public void callArgToBase(Invoke invoke, Context context) {
        // 获取 TaintTransfers
        var transfers = config.getTransfers();
        // 如果 <m, i, base, u> 在 TaintTransfers 中，对于第 i 个实参指向的污点对象集合 c，将 <base, c> 加入到 WorkList 中
        var m = invoke.getMethodRef().resolve();
        assert !invoke.isStatic();
        var base = ((InvokeInstanceExp) invoke.getInvokeExp()).getBase();
        var u = base.getType();
        var pointsToSet = PointsToSetFactory.make();
        for (int i = 0; i < m.getParamCount(); i++) {
            if (!transfers.contains(new TaintTransfer(m, i, TaintTransfer.BASE, u))) {
                continue;
            }
            var arg = invoke.getInvokeExp().getArgs().get(i);
            for (var csObj : csManager.getCSVar(context, arg).getPointsToSet()) {
                if (manager.isTaint(csObj.getObject())) {
                    // 新污点对象的 source call 和原污点对象相同
                    var t = csManager.getCSObj(emptyContext, manager.makeTaint(manager.getSourceCall(csObj.getObject()), u));
                    pointsToSet.addObject(t);
                }
            }
        }
        if (!pointsToSet.isEmpty()) {
            solver.addWorkList(csManager.getCSVar(context, base), pointsToSet);
        }
    }

    public boolean isTaint(Obj obj) {
        return manager.isTaint(obj);
    }
}
