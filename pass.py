"""
Experimenting with a PASS-like strategy for solving string constraints as
quantified arrays with lengths

Requires the "array" branch of pySMT available at:
https://github.com/agriggio/pysmt
"""

import os, sys
from six.moves import cStringIO # Py2-Py3 Compatibility
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.shortcuts import *
import time


STRING_LEN = 'cprover.str.len'

def get_index_set(formula):
    qvar = None
    if formula.is_forall():
        qv = formula.quantifier_vars()
        assert len(qv) == 1
        qvar = qv[0]
        formula = formula.arg(0)
        
    bounds = []

    def has_qvar(a):
        return qvar in a.get_free_variables()

    def dec(t):
        tp = t.get_type()
        assert tp.is_bv_type()
        return BVSub(t, BVOne(tp.width))
    
    def get_ub(f):
        to_process = [f]
        while to_process:
            cur = to_process[-1]
            to_process.pop()
            if cur.is_and():
                to_process += cur.args()
            elif cur.is_bv_ult() and cur.arg(0) == qvar:
                b = cur.arg(1)
                if not has_qvar(b):
                    bounds.append(dec(b))
            elif cur.is_bv_ule():
                b = cur.arg(1)
                if not has_qvar(b):
                    bounds.append(b)

    if qvar is not None:
        assert formula.is_implies()
        get_ub(formula.arg(0))

    ret = {}
    if qvar is not None:
        to_process = [formula.arg(1)]
    else:
        to_process = [formula]
    seen = set()
    while to_process:
        cur = to_process[-1]
        to_process.pop()
        if cur in seen:
            continue
        seen.add(cur)
        if cur.is_select():
            s = cur.arg(0)
            i = cur.arg(1)
            if not has_qvar(i):
                ret.setdefault(s, set(bounds)).add(i)
        else:
            to_process += cur.args()

    return ret


def instantiate(axiom, s, e):
    assert axiom.is_forall()
    assert len(axiom.quantifier_vars()) == 1
    qvar = axiom.quantifier_vars()[0]
    axiom = axiom.arg(0)
    
    body = axiom.arg(1)
    f = None
    to_process = [body]
    while to_process:
        cur = to_process[-1]
        to_process.pop()
        if cur.is_select():
            if cur.arg(0) == s:
                i = cur.arg(1)
                if qvar in i.get_free_variables():
                    f = i
                    break
        else:
            to_process += cur.args()
    if f is None:
        return None

    def getsub(f):
        elems = []
        to_process = [(f, True)]
        while to_process:
            cur, positive = to_process[-1]
            to_process.pop()
            if cur.is_bv_add():
                to_process.append((cur.arg(1), positive))
                to_process.append((cur.arg(0), positive))
            elif cur.is_bv_sub():
                to_process.append((cur.arg(1), not positive))
                to_process.append((cur.arg(0), positive))
            elif cur.is_bv_neg():
                to_process.append((cur.arg(0), not positive))
            else:
                elems.append((cur, positive))

        found = False
        neg = False
        
        width = f.get_type().width
        ret = None
        
        for (t, p) in elems:
            if t == qvar:
                assert not found
                found = True
                neg = not p
            else:
                if not p:
                    t = BVNeg(t)
                if ret is not None:
                    ret = BVAdd(ret, t)
                else:
                    ret = t
        assert found, (to_smt(qvar), to_smt(ret))

        if ret is not None:
            ret = BVSub(e, ret)
        else:
            ret = e
        if neg:
            ret = BVNeg(ret)

        return ret.simplify()

    r = getsub(f)
    print('computed substitution: %s -> %s' % (to_smt(qvar), to_smt(r)))
    return Implies(axiom.arg(0).substitute({qvar : r}),
                   body.substitute({qvar : r}))


def to_smt(f):
    buf = cStringIO()
    p = SmtPrinter(buf)
    p.printer(f)
    return buf.getvalue()


def collect_terms(formula, test):
    ret = set()
    seen = set()
    to_process = [formula]
    while to_process:
        cur = to_process[-1]
        to_process.pop()
        if cur in seen:
            continue
        seen.add(cur)
        if test(cur):
            ret.add(cur)
        to_process += cur.args()
    return ret


def collect_strings(formula):
    return collect_terms(formula,
                         lambda cur: cur.is_function_application() and \
                         cur.function_name().symbol_name() == STRING_LEN)

def collect_flags(formula):
    return collect_terms(formula, lambda cur: cur.is_symbol(types.BOOL))


def get_ground_model(ground, cur):
    solver = Solver()
    for g in ground:
        solver.add_assertion(g)
    for g in cur:
        print('; adding instantiation: %s' % to_smt(g))
        solver.add_assertion(g)
    start = time.time()
    res = solver.solve()
    end = time.time()
    print('; solving time: %.3f' % (end - start))
    if res:
        return solver.get_model()
    else:
        return None


def is_good(model, strings, flags, quantified):
    fmodel = TRUE()
    smodel = []
    for slen in strings:
        l = model.get_value(slen)
        s = slen.arg(0)
        v = model.get_value(s)
        print('; string: %s --> %s' % (to_smt(s), to_smt(v)))
        print('; length: %s --> %s\n' % (to_smt(slen), l.constant_value()))
        fmodel = And(fmodel, And(Equals(slen, l), Equals(s, v)))
        smodel.append((s, l, v))
    for f in flags:
        b = model.get_value(f)
        print('; flag: %s --> %s' % (to_smt(f), b.constant_value()))
        fmodel = And(fmodel, Iff(f, b))
    violated = []
    start = time.time()
    for i, axiom in enumerate(quantified):
        assert axiom.is_forall()
        print('; checking validity of axiom %d' % i)
        m = get_model(And(fmodel, Not(axiom.arg(0))))
        if m is None:
            print(';  axiom is valid')
        else:
            print(';  axiom is NOT valid: %s\n;  witness:' % to_smt(axiom))
            v = axiom.quantifier_vars()[0]
            val = m.get_value(v)
            print(';      %s --> %s' % (to_smt(v), val.constant_value()))
            violated.append((v, val, axiom))
    end = time.time()
    print('; checked axioms in %.3f seconds, %d violated' % \
          ((end - start), len(violated)))
    if len(violated) == 0:
        return True, smodel
    else:
        return False, violated


def print_model(model, strings):
    print('MODEL')
    def getch(v, i):
        f = Select(s, BV(i, 32))
        b = model.get_value(f)
        c = b.constant_value()
        return chr(c)
    seen = set()
    for (s, l, v) in strings:
        val = "".join(getch(s, i) for i in xrange(l.constant_value()))
        print('  %s := "%s"' % (to_smt(s), val.replace('"', '\\"')))
        seen.add(s)
    for (var, value) in model:
        if var not in seen:
            print('  %s := %s' % (to_smt(var), value))

def main():
    parser = SmtLibParser()
    script = parser.get_script(sys.stdin)

    assertions = [cmd.args[0]
                  for cmd in script.filter_by_command_name("assert")]

    ground, quantified = [], []
    strings = set()
    flags = set()
    for f in assertions:
        if f.is_forall():
            assert f.arg(0).is_implies(), f
            quantified.append(f)
            flags |= collect_flags(f)
        else:
            ground.append(f)
        strings |= collect_strings(f)

    print('; Got %d assertions, %d ground and %d quantified, and %d strings' % \
          (len(assertions), len(ground), len(quantified), len(strings)))

    index_set = {}
    cur = assertions
    i = 1
    seen = set()

    while True:
        print('; iteration %d...' % i)
        i += 1

        print('; computing index set from %d formulas' % len(cur))
        index_set = {}
        for formula in cur:
            d = get_index_set(formula)
            index_set.update(d)

        cur = []
            
        for s in index_set:
            for e in index_set[s]:
                for axiom in quantified:
                    inst = instantiate(axiom, s, e)
                    if inst is not None and inst not in seen:
                        cur.append(inst)
                        seen.add(inst)

        print('; adding %d instantiations...' % len(cur))

        model = get_ground_model(ground, cur)
        if model is None:
            print("unsat")
            break
        else:
            ok, info = is_good(model, strings, flags, quantified)
            if ok:
                print_model(model, info)
                print("sat")
                break
            else:
                for (qv, v, axiom) in info:
                    cur.append(axiom.arg(0).substitute({qv : v}))

        ground += cur


if __name__ == '__main__':
    main()
