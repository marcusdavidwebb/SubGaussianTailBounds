#!/usr/bin/env python3
"""Finite rational interface for endpoint lower cost, supplementary S1.5.

Checks every condition in EndpointTableConditions and EndpointFarConditions:
eight positive-width rectangles, 280 tensor coefficients and their exact
expansion identities, four quartic intervals and one derivative interval.
The source digest records independent formula review; it is provenance only.
No integral, probability, matrix or real-variable estimate is a Python premise.
"""
if not __debug__:
    raise SystemExit('Run without -O: assertions are required.')

import ast
import hashlib
import importlib.util
from fractions import Fraction as F
from pathlib import Path
import re
import sys

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('polynomial_interface', HERE / 'check_polynomial_interface.py')
interface = importlib.util.module_from_spec(spec)
spec.loader.exec_module(interface)
original = interface.original
add, scale, mul, power = original.add, original.scale, original.mul, original.ppow
ONE = {(0, 0): F(1)}
K = {(1, 0): F(1)}
X = {(0, 1): F(1)}


def primary_inputs():
    syntax = ast.parse((HERE.parent / 'check_main_constants.py').read_text())
    fn = next(n for n in syntax.body if isinstance(n, ast.FunctionDef) and n.name == 'check_k_one_lower')
    body = []
    for node in fn.body:
        if isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'count' for t in node.targets):
            break
        body.append(node)
    body.append(ast.parse('return poly, rows').body[0])
    args = ast.arguments(posonlyargs=[], args=[], kwonlyargs=[], kw_defaults=[], defaults=[])
    wrapper = ast.FunctionDef(name='inputs', args=args, body=body, decorator_list=[])
    env = dict(vars(original))
    exec(compile(ast.fix_missing_locations(ast.Module(body=[wrapper], type_ignores=[])), __file__, 'exec'), env)
    poly, rows = env['inputs']()
    coeff_node = next(n for n in fn.body if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == 'coeff' for t in n.targets))
    coeff = eval(compile(ast.Expression(coeff_node.value), 'primary quartic', 'eval'), {'F': F})
    return poly, rows, coeff


def constant(q):
    return scale(ONE, q)


def lean_formula(theta, xi, chi, omega):
    """Direct translation of endpointAPoly/GPoly/NPoly/O/NMajorant/Margin.
    Equality with the original checker's independently assembled polynomial
    is checked before any Bernstein test.
    """
    A = add(scale(K, theta), constant((1-theta)*F(73, 55)))
    c = theta+(1-theta)*F(103, 55)
    G = add(mul(add(scale(A, 1/xi), constant(1-c)), X),
            mul(add(A, constant(xi/2), scale(add(power(A, 2), constant(-2*c)), 1/(2*xi))), power(X, 2)),
            scale(mul(add(constant(c), scale(A, c/xi)), power(X, 3)), -1),
            scale(power(X, 4), c*c/(2*xi)))
    N = add(mul(add(scale(A, 2/chi), constant(-c)), X),
            mul(add(constant(chi), scale(add(power(A, 2), constant(-2*c)), 1/chi)), power(X, 2)),
            scale(mul(A, power(X, 3)), -2*c/chi), scale(power(X, 4), c*c/chi))
    # Polynomial evaluation at inner X sets both variables to K.
    G_at_K = {}
    for (a, x), v in G.items():
        G_at_K[a+x, 0] = G_at_K.get((a+x, 0), F(0))+v
    rest = add(ONE, scale(power(K, 2), -1))
    O = add(A, constant(1/(2*xi)), mul(power(K, 2), G_at_K), mul(rest, G))
    d = mul(K, add(ONE, mul(A, K), scale(power(K, 2), -c)))
    NM = add(A, scale(power(K, 3), -c), scale(mul(power(K, 2), d), 2), scale(rest, 1/chi), mul(rest, N))
    return add(constant(F(73, 50)), scale(O, -omega), scale(NM, -(1-omega)))


def interval_certificate(p, a, b, degree):
    assert a < b
    q = interface.transformed(p, a, b, F(0), F(1))
    bs = interface.coefficients(q, degree, 0)
    interface.verify_expansion(q, degree, 0, bs)
    assert min(map(min, bs)) > 0
    return degree+1


def main():
    source = HERE / 'SingularValueBounds/KL/Lower/EndpointCertificates.lean'
    digest = hashlib.sha256(source.read_bytes()).hexdigest()
    assert digest == SOURCE_DIGEST, 'EndpointCertificates changed: review formula correspondence before updating provenance.'
    original_poly, rows, far = primary_inputs()
    text = source.read_text()
    # Match the finite row data to the actual primary table, not a second
    # unchecked table. The notation is intentionally narrow and inspectable.
    for name, position in [('Theta',2), ('Chi',4), ('Omega',5), ('KLo',0), ('KHi',1)]:
        match = re.search(r'def endpoint'+name+r'.*?: ℚ := if i = 0 then ([0-9/]+) else ([0-9/]+)', text)
        assert match, name
        assert [F(match.group(1)), F(match.group(2))] == [row[position] for row in rows]
    assert 'def endpointXi (_ : Fin 2) : ℚ := 8/5' in text
    assert all(row[3] == F(8, 5) for row in rows)
    count = 0
    for kl, kh, theta, xi, chi, omega in rows:
        p = lean_formula(theta, xi, chi, omega)
        assert p == original_poly(theta, xi, chi, omega)
        assert max(a for a,x in p) == 6 and max(x for a,x in p) == 4
        for j in range(4):
            box = kl, kh, F(7*j,40), F(7*(j+1),40)
            assert box[0] < box[1] and box[2] < box[3]
            q = interface.transformed(p, *box)
            bs = interface.coefficients(q, 6, 4)
            interface.verify_expansion(q, 6, 4, bs)
            assert min(map(min, bs)) > F(1,5000)
            count += 35
    assert count == 280
    g = {(j,0): value for j,value in enumerate(far) if value}
    gap = add(constant(F(7,100)), scale(g,-1))
    knots = [F(0),F(1,4),F(3,8),F(1,2),F(1)]
    scalar_count = sum(interval_certificate(gap,a,b,4) for a,b in zip(knots,knots[1:]))
    derivative = {(0,0):F(7,50), **{(j,0):-(j+2)*far[j] for j in range(1,5)}}
    assert derivative == {(0,0):F(7,50),(1,0):-F(3,32),(2,0):-F(1849,320),(3,0):F(1995,128),(4,0):-F(735,128)}
    scalar_count += interval_certificate(derivative,F(3,4),F(1),4)
    assert scalar_count == 25
    # Mutation checks exercise rejection by the finite acceptance predicate.
    altered = add(lean_formula(*rows[0][2:]),constant(-100))
    bad = interface.coefficients(interface.transformed(altered,rows[0][0],rows[0][1],F(0),F(7,40)),6,4)
    assert min(map(min,bad)) < 0
    try:
        interface.verify_expansion({(0,0):F(1)},0,0,[[F(2)]])
    except AssertionError:
        pass
    else:
        raise AssertionError('Altered Bernstein identity was accepted')
    original.check_k_one_lower()
    print(f'PASS: EndpointTableConditions 8 boxes/{count} tensor signs+identities; EndpointFarConditions 5 intervals/{scalar_count} signs+identities; source {digest}.')


SOURCE_DIGEST = '1f5b6e746aa7787bd35495799c5f9349b362bfbba1a5a54d12792b037d98494c'
if __name__ == '__main__':
    main()
