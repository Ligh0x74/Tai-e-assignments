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

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.ArrayDeque;
import java.util.HashSet;
import java.util.Queue;
import java.util.Set;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        // corner case, entry is null
        if (entry == null) {
            return callGraph;
        }
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> q = new ArrayDeque<>();
        q.offer(entry);
        while (!q.isEmpty()) {
            var m = q.poll();
            if (!callGraph.addReachableMethod(m)) {
                continue;
            }
            callGraph.callSitesIn(m).forEach(cs -> {
                resolve(cs).forEach(t -> {
                    callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(cs), cs, t));
                    q.offer(t);
                });
            });
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        var res = new HashSet<JMethod>();
        var c = callSite.getMethodRef().getDeclaringClass();
        var s = callSite.getMethodRef().getSubsignature();

        if (callSite.isStatic()) {
            res.add(c.getDeclaredMethod(s));
        } else if (callSite.isSpecial()) {
            res.add(dispatch(c, s));
        } else if (callSite.isVirtual() || callSite.isInterface()) {
            Queue<JClass> q = new ArrayDeque<>();
            q.offer(c);
            // 注意 interface 的处理, 包含直接实现和间接实现的情况
            while (!q.isEmpty()) {
                c = q.poll();
                res.add(dispatch(c, s));
                if (c.isInterface()) {
                    hierarchy.getDirectSubinterfacesOf(c).forEach(q::offer);
                    hierarchy.getDirectImplementorsOf(c).forEach(q::offer);
                } else {
                    hierarchy.getDirectSubclassesOf(c).forEach(q::offer);
                }
            }
        }
        // 删除 dispatch 返回值为 null 的情况
        res.remove(null);
        return res;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        if (jclass == null) {
            return null;
        }
        var m = jclass.getDeclaredMethod(subsignature);
        if (m == null) {
            return dispatch(jclass.getSuperClass(), subsignature);
        }
        // 过滤抽象方法
        return m.isAbstract() ? null : m;
    }
}
