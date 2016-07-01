#!/usr/bin/env python
import sys
import sexpdata
Symbol = sexpdata.Symbol

def convert_eq(l):
    c1, t1 = convert(l[1])
    c2, t2 = convert(l[2])
    assert t1 == t2
    if t1 == str:
        return '__CPROVER_string_equal(%s, %s)' % (c1, c2), None
    else:
        return '(%s == %s)' % (c1, c2), None

def convert_str(s):
    return ('__CPROVER_string_literal("%s")' % s), str

def convert_int(s):
    return str(s), int

def convert_var(s):
    return str(s.value()), get_type(s)

def convert_len(s):
    return '__CPROVER_string_length(%s)' % convert(s[1])[0], int

def convert_or(s):
    return '(%s)' % ' || '.join(convert(c)[0] for c in s[1:]), None

def convert_not(s):
    return '!(%s)' % convert(s[1])[0], None

def convert_bvadd(s):
    return '(%s + %s)' % (convert(s[1])[0], convert(s[2])[0]), int

def convert_concat(s):
    return '__CPROVER_string_concat(%s, %s)' % \
           (convert(s[1])[0], convert(s[2])[0]), str

def convert_sle(s):
    return '((int)%s) <= ((int)%s)' % (convert(s[1])[0], convert(s[2])[0]), None

def convert_ule(s):
    return '((unsigned)%s) <= ((unsigned)%s)' % \
           (convert(s[1])[0], convert(s[2])[0]), None
    
def convert_slt(s):
    return '((int)%s) < ((int)%s)' % (convert(s[1])[0], convert(s[2])[0]), None

def convert_ult(s):
    return '((unsigned)%s) < ((unsigned)%s)' % \
           (convert(s[1])[0], convert(s[2])[0]), None

def convert_sge(s):
    return '((int)%s) >= ((int)%s)' % (convert(s[1])[0], convert(s[2])[0]), None

def convert_uge(s):
    return '((unsigned)%s) >= ((unsigned)%s)' % \
           (convert(s[1])[0], convert(s[2])[0]), None
    
def convert_sgt(s):
    return '((int)%s) > ((int)%s)' % (convert(s[1])[0], convert(s[2])[0]), None

def convert_ugt(s):
    return '((unsigned)%s) > ((unsigned)%s)' % \
           (convert(s[1])[0], convert(s[2])[0]), None

def convert_hex(s):
    v = s.value()
    assert v.startswith('#x')
    return str(int(v[2:], 16)), int

def convert_bvnum(s):
    assert len(s) == 3
    assert s[0].value() == '_'
    assert s[2] == 32
    val = int(s[1].value()[2:])
    return str(val), int
    

convmap = {
    u'=' : convert_eq,
    u'strlen_bv' : convert_len,
    u'Length' : convert_len,
    u'or' : convert_or,
    u'bvadd' : convert_bvadd,
    u'Concat' : convert_concat,
    u'bvsle' : convert_sle,
    u'bvslt' : convert_slt,
    u'bvsge' : convert_sge,
    u'bvsgt' : convert_sgt,
    u'bvule' : convert_ule,
    u'bvult' : convert_ult,
    u'bvuge' : convert_uge,
    u'bvugt' : convert_ugt,
    u'not' : convert_not,
    }

def convert(s):
    if isinstance(s, Symbol):
        if s.value().startswith('#x'):
            return convert_hex(s)
        else:
            return convert_var(s)
    elif isinstance(s, (str, unicode)):
        return convert_str(s)
    elif isinstance(s, int):
        return convert_int(s)
    else:
        assert isinstance(s, list) and len(s) > 0
        h = s[0]
        assert isinstance(h, Symbol)
        try:
            f = convmap[h.value()]
            return f(s)
        except KeyError:
            if h.value() == u'_':
                return convert_bvnum(s)
            else:
                raise

varmap = {}

def get_type(s):
    return varmap[s.value()]

def to_type(tp):
    if tp == str:
        return '__CPROVER_string'
    elif tp == int:
        return 'unsigned int'
    else:
        assert False, tp

def main(src):
    with open(src) as f:
        data = '(' + f.read() + ')'
    sexp = sexpdata.loads(data)
    constrs = []
    for s in sexp:
        if s[0].value() == u'declare-variable':
            name = s[1].value()
            t = s[2]
            if isinstance(t, Symbol):
                if t.value() == u'String':
                    tp = str
                elif t.value() == u'Int':
                    tp = int
            elif isinstance(t, list) and t[0].value() == u'_' \
                 and t[1].value() == u'BitVec':
                assert t[2] == 32
                tp = int
            else:
                assert False, t
            varmap[name] = tp
        elif s[0].value() == u'assert':
            c, _ = convert(s[1])
            constrs.append(c)

    pr = sys.stdout.write

    pr('#include <assert.h>\n')
    pr('#include "../../cprover-string-hack.h"\n\n')
    pr('int main()\n{\n')
    for name in sorted(varmap):
        if varmap[name] is not None:
            pr('  %s %s;\n' % (to_type(varmap[name]), name))
    pr('\n')
    pr('  if (%s) {\n    assert(0);\n  }\n  return 0;\n}\n' %
       '\n      && '.join(constrs))


if __name__ == '__main__':
    try:
        main(sys.argv[1])
    except:
        sys.stderr.write('ERROR: %s\n' % sys.argv[1])
        raise

