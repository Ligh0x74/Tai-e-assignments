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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.ArithmeticExp;
import pascal.taie.ir.exp.BinaryExp;
import pascal.taie.ir.exp.BitwiseExp;
import pascal.taie.ir.exp.ConditionExp;
import pascal.taie.ir.exp.Exp;
import pascal.taie.ir.exp.IntLiteral;
import pascal.taie.ir.exp.ShiftExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        var fact = new CPFact();
        for (var v : cfg.getIR().getParams()) {
            if (canHoldInt(v)) {
                fact.update(v, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        fact.forEach((k, v) -> {
            target.update(k, meetValue(v, target.get(k)));
        });
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef()) {
            return v2;
        }
        if (v2.isUndef()) {
            return v1;
        }
        return v1.equals(v2) ? v1 : Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        if (stmt.getDef().isEmpty() || !(stmt.getDef().get() instanceof Var l) || !canHoldInt(l)) {
            return out.copyFrom(in);
        }

        in = in.copy();
        var r = ((DefinitionStmt) stmt).getRValue();
        if (r instanceof IntLiteral) {
            in.update(l, Value.makeConstant(((IntLiteral) r).getValue()));
        } else if (r instanceof Var) {
            in.update(l, in.get((Var) r));
        } else {
            in.update(l, evaluate(r, in));
        }
        return out.copyFrom(in);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (!(exp instanceof BinaryExp binaryExp)) {
            return Value.getNAC();
        }

        var v1 = in.get(binaryExp.getOperand1());
        var v2 = in.get(binaryExp.getOperand2());

        // corner case, v1 = NAC, v2 = 0
        if (exp instanceof ArithmeticExp e && v2.isConstant() && v2.getConstant() == 0) {
            switch (e.getOperator()) {
                case DIV, REM:
                    return Value.getUndef();
            }
        }

        if (v1.isNAC() || v2.isNAC()) {
            return Value.getNAC();
        }
        if (v1.isUndef() || v2.isUndef()) {
            return Value.getUndef();
        }

        int res = 0;
        var c1 = v1.getConstant();
        var c2 = v2.getConstant();
        if (exp instanceof ArithmeticExp e) {
            switch (e.getOperator()) {
                case ADD:
                    res = c1 + c2;
                    break;
                case SUB:
                    res = c1 - c2;
                    break;
                case MUL:
                    res = c1 * c2;
                    break;
                case DIV:
                    res = c1 / c2;
                    break;
                case REM:
                    res = c1 % c2;
                    break;
                default:
                    break;
            }
        }
        else if (exp instanceof ConditionExp e) {
            switch (e.getOperator()) {
                case EQ:
                    res = c1 == c2 ? 1 : 0;
                    break;
                case NE:
                    res = c1 != c2 ? 1 : 0;
                    break;
                case LT:
                    res = c1 < c2 ? 1 : 0;
                    break;
                case GT:
                    res = c1 > c2 ? 1 : 0;
                    break;
                case LE:
                    res = c1 <= c2 ? 1 : 0;
                    break;
                case GE:
                    res = c1 >= c2 ? 1 : 0;
                    break;
                default:
                    break;
            }
        }
        else if (exp instanceof ShiftExp e) {
            switch (e.getOperator()) {
                case SHL:
                    res = c1 << c2;
                    break;
                case SHR:
                    res = c1 >> c2 ;
                    break;
                case USHR:
                    res = c1 >>> c2;
                    break;
                default:
                    break;
            }
        }
        else if (exp instanceof BitwiseExp e) {
            switch (e.getOperator()) {
                case OR:
                    res = c1 | c2;
                    break;
                case AND:
                    res = c1 & c2;
                    break;
                case XOR:
                    res = c1 ^ c2;
                    break;
                default:
                    break;
            }
        }
        return Value.makeConstant(res);
    }
}
