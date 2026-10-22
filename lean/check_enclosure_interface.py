#!/usr/bin/env python3
"""Exact finite checks for the P07 Lean/Python enclosure interface.

The two pilot inputs match the literal examples in
SingularValueBounds/KL/Certificates/Enclosures.lean. Lean proves that the
finite certificate conditions imply the analytic enclosures; this script
checks the concrete rational conditions externally. It also reproduces the
three scalar exponential comparisons used by P09. This is not a check of
all numerical certificates in the supplementary theorem.
"""

from fractions import Fraction as F
from math import factorial


def exp_sum(x: F, order: int) -> F:
    return sum((x**j / factorial(j) for j in range(order + 1)), F(0))


def exp_bounds(x: F, order: int) -> tuple[F, F]:
    assert order >= 0 and 0 <= x < order + 2
    lower = exp_sum(x, order)
    upper = lower + x ** (order + 1) / factorial(order + 1) / (
        1 - x / (order + 2)
    )
    return lower, upper


def log_ratio_bounds(z: F, order: int) -> tuple[F, F]:
    assert order >= 1 and 0 <= z < 1
    lower = 2 * sum(
        (z ** (2 * j + 1) / (2 * j + 1) for j in range(order)), F(0)
    )
    upper = lower + 2 * z ** (2 * order + 1) / (
        (2 * order + 1) * (1 - z**2)
    )
    return lower, upper


def main() -> None:
    if not __debug__:
        raise RuntimeError("Verification requires Python assertions enabled.")

    # Exp pilot: x=1/2, N=24, outward-rounded rational endpoints.
    lo, hi = exp_bounds(F(1, 2), 24)
    assert F(1648721270700, 10**12) <= lo
    assert hi <= F(1648721270701, 10**12)
    print("PASS P07.exp_half: finite rational exponential certificate")

    # Log pilot: z=1/3, N=18, hence log((1+z)/(1-z))=log 2.
    lo, hi = log_ratio_bounds(F(1, 3), 18)
    assert F(693147180559, 10**12) <= lo
    assert hi <= F(693147180560, 10**12)
    print("PASS P07.log_two: finite rational logarithm certificate")

    assert exp_bounds(F(751, 250), 24)[0] > F(1996, 99)
    assert exp_bounds(F(3), 24)[1] < 21
    assert exp_bounds(F(259, 80), 24)[0] > F(499, 20)
    assert F(499, 100) < 2 * F(79, 50) ** 2
    assert F(5, 2) < 2 * F(28, 25) ** 2
    print("PASS P09.offset_and_beta: scalar exponential and rational checks")


if __name__ == "__main__":
    main()
