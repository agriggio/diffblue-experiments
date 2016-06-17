"""
Experimenting with a PASS-like strategy for solving string constraints as
quantified arrays with lengths

Requires pySMT: https://github.com/pysmt/pysmt
"""

import os, sys
from six.moves import cStringIO # Py2-Py3 Compatibility
from pysmt.smtlib.parser import SmtLibParser
from pysmt.smtlib.printers import SmtPrinter, SmtDagPrinter
from pysmt.smtlib import commands
from pysmt.shortcuts import *
from pysmt import logics
import time
import argparse


STRING_LEN = 'cprover.str.len'
VERBOSITY = 0

def msg(lvl, fmt, *args):
    if VERBOSITY >= lvl:
        print(fmt % tuple(args))

def info(fmt, *args):
    msg(1, fmt, *args)

def debug(fmt, *args):
    msg(2, fmt, *args)

def show(fmt, *args):
    msg(0, fmt, *args)
    

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
    debug('computed substitution: %s -> %s', to_smt(qvar), to_smt(r))
    return Implies(axiom.arg(0).substitute({qvar : r}),
                   body.substitute({qvar : r}))


class to_smt(object):
    def __init__(self, f):
        self.f = f

    def __str__(self):
        buf = cStringIO()
        p = SmtPrinter(buf)
        p.printer(self.f)
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


def get_ground_model(solver, ground, cur):
    #solver = Solver()
    #solver.push()
    ## for g in ground:
    ##     solver.add_assertion(g)
    for g in cur:
        debug('; adding instantiation: %s', to_smt(g))
        solver.add_assertion(g)
    start = time.time()
    res = solver.solve()
    end = time.time()
    info('; solving time: %.3f' % (end - start))
    m = None
    if res:
        m = solver.get_model()
    #solver.pop()
    return m


def is_good(solver, model, strings, flags, quantified):
    fmodel = TRUE()
    smodel = []
    for slen in strings:
        l = model.get_value(slen)
        s = slen.arg(0)
        v = model.get_value(s)
        debug('; string: %s --> %s', to_smt(s), to_smt(v))
        debug('; length: %s --> %s', to_smt(slen), l.constant_value())
        fmodel = And(fmodel, And(Equals(slen, l), Equals(s, v)))
        smodel.append((s, l, v))
    for f in flags:
        b = model.get_value(f)
        debug('; flag: %s --> %s', to_smt(f), b.constant_value())
        fmodel = And(fmodel, Iff(f, b))
    violated = []
    start = time.time()
    solver.reset_assertions()
    solver.add_assertion(fmodel)
    for i, axiom in enumerate(quantified):
        assert axiom.is_forall()
        debug('; checking validity of axiom %d', i)
        solver.push()
        f = Not(axiom.arg(0))
        solver.add_assertion(f)
        if solver.solve():
            m = solver.get_model()
        else:
            m = None
        if m is None:
            debug(';  axiom is valid')
        else:
            debug(';  axiom is NOT valid: %s\n;  witness:', to_smt(axiom))
            v = axiom.quantifier_vars()[0]
            val = m.get_value(v)
            debug(';      %s --> %s', to_smt(v), val.constant_value())
            violated.append((v, val, axiom))
        solver.pop()
    end = time.time()
    info('; checked %d axioms in %.3f seconds, %d violated',
         len(quantified), (end - start), len(violated))
    if len(violated) == 0:
        return True, smodel
    else:
        return False, violated


def show_model(model, strings):
    show('MODEL')
    def getch(v, i):
        f = Select(s, BV(i, 32))
        b = model.get_value(f)
        c = b.constant_value()
        return chr(c)
    seen = set()
    for (s, l, v) in strings:
        n = l.constant_value()
        if n is None:
            show('  WARNING: no value for %s', to_smt(s))
        else:
            if n > 50:
                extra = "[...] (50 of %d chars shown)" % n
                n = 50
            else:
                extra = ""
            val = "".join(getch(s, i) for i in xrange(n))
            show('  %s := "%s"%s', to_smt(s), val.replace('"', '\\"'), extra)
        seen.add(s)
    for (var, value) in model:
        if var not in seen:
            show('  %s := %s', to_smt(var), value)

def main(opts):
    start = time.time()
    parser = SmtLibParser()
    with open(opts.filename) as src:
        script = parser.get_script(src)

    assertions = [cmd.args[0]
                  for cmd in script.filter_by_command_name(commands.ASSERT)]

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

    info('; Got %d assertions, %d ground and %d quantified, and %d strings',
         len(assertions), len(ground), len(quantified), len(strings))

    index_set = {}
    cur = assertions
    i = 1
    seen = set()

    mainsolver = Solver(name=opts.solver, logic=logics.QF_AUFBV)
    modelsolver = Solver(name=opts.solver, logic=logics.QF_AUFBV)

    for g in ground:
        mainsolver.add_assertion(g)

    while True:
        info('; iteration %d...', i)
        i += 1

        info('; computing index set from %d formulas', len(cur))
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

        info('; adding %d instantiations...', len(cur))

        model = get_ground_model(mainsolver, ground, cur)
        if model is None:
            show("unsat")
            break
        else:
            ok, extra = is_good(modelsolver, model, strings, flags, quantified)
            if ok:
                if VERBOSITY > 0:
                    show_model(model, extra)
                show("sat")
                if opts.get_values:
                    for cmd in \
                            script.filter_by_command_name(commands.GET_VALUE):
                        try:
                            vals = ["(%s %s)" % (to_smt(t),
                                                 to_smt(model.get_value(t)))
                                    for t in cmd.args]
                            show("(%s)", " ".join(vals))
                        except Exception, e:
                            show('(error "%s")', str(e).replace('"', '\\"'))
                break
            else:
                for (qv, v, axiom) in extra:
                    inst = axiom.arg(0).substitute({qv : v})
                    if inst not in seen:
                        cur.append(inst)
                        seen.add(inst)
                        mainsolver.add_assertion(inst)

        ground += cur
    end = time.time()
    info("; total time: %.3f", (end - start))


def getopts():
    p = argparse.ArgumentParser()
    p.add_argument('--verbosity', type=int, help='set verbosity level',
                   default=1)
    p.add_argument('--get-values', action='store_true',
                   help='evalate the get-value commands if the result is sat')
    solvers = sorted(get_env().factory.all_solvers(logics.QF_AUFBV).keys())
    p.add_argument('--solver', help='set the underlying solver to use',
                   choices=solvers)
    p.add_argument('filename', help='input file')
    ret = p.parse_args()
    global VERBOSITY
    VERBOSITY = ret.verbosity
    return ret

if __name__ == '__main__':
    #raw_input('enter... %d: ' % os.getpid())
    main(getopts())
