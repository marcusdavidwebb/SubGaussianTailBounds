#!/usr/bin/env python3
"""Finite rational certificate for the endpoint upper-MGF logarithmic ratio.

Checks the exact polynomial, affine change, tensor Bernstein identity and
coefficient signs named in EndpointLogratio.lean. No derivative, integral,
probabilistic or matrix assertion is checked by Python.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from check_polynomial_interface import (
    add, scale, mul, power, transformed, coefficients, verify_expansion,
)


def main():
    if not __debug__:
        raise SystemExit("Run without -O; assertions implement the finite checks.")
    one = {(0, 0): F(1)}
    a = {(1, 0): F(1)}
    x = {(0, 1): F(1)}
    z = scale(add(x, mul(a, power(x, 2)), scale(power(x, 3), -2)), F(12, 5))
    zp = scale(add(one, scale(mul(a, x), 2), scale(power(x, 2), -6)), F(12, 5))
    d = add(one, scale(z, -F(16, 7)), scale(power(z, 2), F(12, 7)),
            scale(power(z, 3), -F(16, 35)), scale(power(z, 4), F(1, 35)))
    n = add(z, scale(power(z, 2), -F(25, 14)),
            scale(power(z, 3), F(19, 21)), scale(power(z, 4), -F(47, 420)))
    p = add(mul(mul(mul(x, zp), z), d),
            scale(mul(add(n, scale(mul(z, d), -1)), add(one, scale(z, -1))), -2))
    assert max(i for i, j in p) <= 6
    assert max(j for i, j in p) <= 18
    assert all(j >= 3 for i, j in p)
    box = (F(1, 2), F(1), F(0), F(7, 20))
    affine = transformed(p, *box)
    bs = coefficients(affine, 6, 18)
    assert all(value >= 0 for row in bs for value in row)
    verify_expansion(affine, 6, 18, bs)
    quotient = {(i, j - 3): value for (i, j), value in p.items()}
    qbs = coefficients(transformed(quotient, *box), 6, 15)
    assert min(map(min, qbs)) > F(49, 500)
    print("PASS: endpoint logratio; exact 7 x 19 tensor identity and signs; quotient margin >49/500.")


if __name__ == "__main__":
    main()
