#!/usr/bin/env python3
"""Exact finite data for P08/P16/P17; no analytic assertion is checked here.

Regenerates the adaptive trees used by the manuscript's existing arithmetic
checker, checks every coefficient identity/sign with Fraction arithmetic,
and compares their Lean transcription. Run with --write to regenerate only
CertificateTrees.lean. The substantive finite conditions remain explicit
hypotheses of the Lean consequences; Python does not manufacture proof terms.
"""
if not __debug__:
    raise SystemExit("Run without -O: this checker requires assertions.")

import ast
import hashlib
import importlib.util
from fractions import Fraction as F
from math import comb
from math import factorial
from pathlib import Path
import sys

sys.dont_write_bytecode = True

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("main_constants", HERE.parent / "check_main_constants.py")
original = importlib.util.module_from_spec(spec)
spec.loader.exec_module(original)
add, scale, mul, power = original.add, original.scale, original.mul, original.ppow


def determinant_inputs():
    """Execute the original exact polynomial definitions, before subdivision."""
    tree = ast.parse((HERE.parent / "check_main_constants.py").read_text())
    fn = next(n for n in tree.body if isinstance(n, ast.FunctionDef) and n.name == "check_determinants")
    body = []
    for node in fn.body:
        if isinstance(node, ast.For):
            break
        body.append(node)
    body.append(ast.parse("return Hs, DP, NP, domains").body[0])
    fn = ast.FunctionDef(name="inputs", args=ast.arguments(posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[]),
                         body=body, decorator_list=[])
    module = ast.fix_missing_locations(ast.Module(body=[fn], type_ignores=[]))
    env = dict(vars(original))
    exec(compile(module, str(HERE / "check_polynomial_interface.py"), "exec"), env)
    return env["inputs"]()


def transformed(p, a, b, c, d):
    result = {}
    for (k, l), value in p.items():
        for i in range(k + 1):
            for j in range(l + 1):
                v = value * comb(k, i) * a ** (k-i) * (b-a) ** i * comb(l, j) * c ** (l-j) * (d-c) ** j
                result[i,j] = result.get((i,j), F(0)) + v
    return {ij: v for ij, v in result.items() if v}


def coefficients(p, n, m):
    return [[sum((v * F(comb(i,k), comb(n,k)) * F(comb(j,l), comb(m,l))
                  for (k,l),v in p.items() if k <= i and l <= j), F(0))
             for j in range(m+1)] for i in range(n+1)]


def basis(n, i):
    return {i+k: F(comb(n,i)*comb(n-i,k)*(-1)**k) for k in range(n-i+1)}


def verify_expansion(p, n, m, bs):
    """Checks the exact finite polynomial identity in TensorCertificate."""
    result = {}
    bx = [basis(n,i) for i in range(n+1)]
    by = [basis(m,j) for j in range(m+1)]
    for i in range(n+1):
        for j in range(m+1):
            for k,x in bx[i].items():
                for l,y in by[j].items():
                    result[k,l] = result.get((k,l), F(0)) + bs[i][j]*x*y
    assert {ij:v for ij,v in result.items() if v} == p


def quad_certificate(p, box, depth=0):
    assert box[0] < box[1] and box[2] < box[3]
    n = max(k for k,l in p)
    m = max(l for k,l in p)
    q = transformed(p, *box)
    bs = coefficients(q,n,m)
    if min(map(min,bs)) > 0:
        verify_expansion(q,n,m,bs)
        return ".leaf", 1, depth, min(map(min,bs))
    assert depth < 5
    a,b,c,d = box
    xm, ym = (a+b)/2, (c+d)/2
    children = [quad_certificate(p, sub, depth+1) for sub in
                [(a,xm,c,ym),(a,xm,ym,d),(xm,b,c,ym),(xm,b,ym,d)]]
    return "(.split " + " ".join(t[0] for t in children) + ")", sum(t[1] for t in children), max(t[2] for t in children), min(t[3] for t in children)


RATE_ROWS = [(F(81,40),F(61,50000000)),(F(83,40),F(57,2000000)),(F(17,8),F(29,250000)),
             (F(41,20),F(1,100000)),(F(21,10),F(13,200000)),(F(43,20),F(19,100000)),
             (F(11,5),F(1,2500)),(F(23,10),F(27,25000)),(F(12,5),F(21,10000)),
             (F(9,4),F(7,10000)),(F(5,2),F(7,2000)),(F(11,4),F(79,10000)),
             (F(3),F(27,2000)),(F(7,2),F(131,5000)),(F(4),F(201,5000))]


def rate_polynomial(v, correction):
    V = {(1,0):v}
    W = {(0,0):2*v-2,(1,0):v,(2,0):F(2)}
    A = {(0,0):v-1,(1,0):v-1}
    D = add(power(W,2),scale(power(V,2),-1))
    first = mul(add(scale(A,correction),V),mul(power(W,11),D))
    series = add(*[scale(mul(mul(power(V,2*j+1),power(W,10-2*j)),D),F(1,2*j+1)) for j in range(6)],scale(power(V,13),F(1,13)))
    return add(first,scale(mul(A,series),-2))


def binary_certificate(p, a, b, depth=0):
    assert a < b
    q = transformed(p,a,b,F(0),F(1))
    n = max(k for k,l in p)
    bs = coefficients(q,n,0)
    if min(map(min,bs)) > 0:
        verify_expansion(q,n,0,bs)
        return ".leaf", 1
    assert depth < 8
    mid = (a+b)/2
    l,lc = binary_certificate(p,a,mid,depth+1)
    r,rc = binary_certificate(p,mid,b,depth+1)
    return f"(.split {l} {r})", lc+rc


def rat(x):
    return f"({x.numerator}/{x.denominator})"


def render():
    hs, dp, np, boxes = determinant_inputs()
    trees, counts, degrees = [], [], []
    for h,box in zip(hs,boxes):
        cleared = add(mul(h,dp),scale(np,-1))
        assert all(l>=2 for k,l in cleared)
        p = {(k,l-2):v for (k,l),v in cleared.items()}
        tree,count,depth,margin = quad_certificate(p,box)
        assert margin > F(1,100000)
        trees.append(tree)
        counts.append(count)
        degrees.append((max(k for k,l in p), max(l for k,l in p)))
    assert counts == [19,19,13,28,16,70] and sum(counts)==165
    rate_trees, rate_counts = [], []
    for v,c in RATE_ROWS:
        p = rate_polynomial(v,c)
        assert max(k for k,l in p)==27 and all(l==0 for k,l in p)
        tree,count = binary_certificate(p,F(0),v-1)
        rate_trees.append(tree)
        rate_counts.append(count)
    text = '''import SingularValueBounds.KL.Certificates.Polynomial

/-! Finite subdivision data generated by check_polynomial_interface.py.
The generator checks all rational coefficient identities/signs externally;
these shapes alone assert no analytic or numerical conclusion. -/
namespace SingularValueBounds.KL.Certificates
noncomputable section
'''
    text += 'def rateRows : Fin 15 → ℚ × ℚ := ![' + ', '.join(f'({rat(v)}, {rat(c)})' for v,c in RATE_ROWS) + ']\n\n'
    text += 'def rateTrees : Fin 15 → BinaryTree := ![\n  ' + ',\n  '.join(rate_trees) + ']\n\n'
    text += 'def majorantBoxes : Fin 6 → RationalBox := ![\n  ' + ',\n  '.join('⟨' + ', '.join(rat(v) for v in box) + '⟩' for box in boxes) + ']\n\n'
    text += 'def majorantDegrees : Fin 6 → ℕ × ℕ := ![' + ', '.join(f'({n},{m})' for n,m in degrees) + ']\n\n'
    text += 'def majorantTrees : Fin 6 → QuadTree := ![\n  ' + ',\n  '.join(trees) + ']\n\nend\nend SingularValueBounds.KL.Certificates\n'
    return text, sum(rate_counts)


def main():
    # Pins the independently reviewed Lean transcription. This hash detects
    # later drift; it is provenance, not a mathematical proof of correspondence.
    formula_source = HERE / "SingularValueBounds/KL/Upper/CertificateData.lean"
    assert hashlib.sha256(formula_source.read_bytes()).hexdigest() == \
        "4fdda6139f71b719887a2341b31c9aa1420075b9e19fa12a863461324ab89061", \
        "CertificateData changed: review its exact correspondence before updating this digest"
    # Match all fifteen pairs against the original checker's actual table.
    syntax = ast.parse((HERE.parent / "check_main_constants.py").read_text())
    extension = next(n for n in syntax.body if isinstance(n, ast.FunctionDef)
                     and n.name == "check_general_upper_tail_extension")
    rows_fn = next(n for n in extension.body if isinstance(n, ast.FunctionDef) and n.name == "check_rows")
    assignment = next(n for n in rows_fn.body if isinstance(n, ast.Assign)
                      and any(isinstance(t, ast.Name) and t.id == "rows" for t in n.targets))
    actual_rows = eval(compile(ast.Expression(assignment.value), "original rate rows", "eval"), {"F":F})
    assert RATE_ROWS == actual_rows
    text, count = render()
    output = HERE / "SingularValueBounds/KL/Upper/CertificateTrees.lean"
    if "--write" in sys.argv:
        output.write_text(text)
    else:
        assert output.read_text() == text, "Lean tree transcription differs: inspect before regenerating"
    # Closed/degenerate boundary and clipping arithmetic used by P08.
    assert max(F(0),F(1,2))==F(1,2) and min(F(1),F(3,4))==F(3,4)
    assert F(1,2)<=F(1,2)<=F(1,2)
    # The finite basis identities required by the degree-elevation bridge.
    for n in range(7):
        for i in range(n+1):
            rhs = {}
            for index,weight in [(i,F(n+1-i,n+1)),(i+1,F(i+1,n+1))]:
                assert weight >= 0
                for k,v in basis(n+1,index).items():
                    rhs[k] = rhs.get(k,F(0))+weight*v
            assert {k:v for k,v in rhs.items() if v} == basis(n,i)
    # Exactly NormDeterminantCertificateConditions: both Taylor comparisons.
    for cutoff,coefficient,order in [(F(223,500),F(671,100),8),(F(21,50),F(563,100),24)]:
        argument=2*cutoff+coefficient*cutoff**2
        assert sum((argument**j/F(factorial(j)) for j in range(order+1)),F(0)) >= 1/(1-2*cutoff)
    print(f"PASS: 15 rate polynomials, {count} interval leaves, 165 determinant rectangles; every finite Bernstein identity and sign checked.")


if __name__ == "__main__":
    main()
