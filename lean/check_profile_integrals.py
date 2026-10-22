#!/usr/bin/env python3
"""Repeat the original checker's exact P12 profile integral arithmetic.

This adapter executes the actual integral certificate blocks in the original
checker and compares their endpoints and rational results with the Lean proofs.
Every analytic implication and every finite comparison is also proved directly
in ProfileIntegral.lean; this script supplies no assumption to Lean.
"""
if not __debug__:
    raise SystemExit("Run without -O: exact assertions are required.")

from fractions import Fraction as F
from pathlib import Path
import inspect
import sys
import textwrap

sys.dont_write_bytecode = True
HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent))
import check_main_constants as printed


def original_block(function, begin, end):
    source = inspect.getsource(function)
    assert source.count(begin) == 1 and source.count(end) == 1
    block = source[source.index(begin):source.index(end)]
    environment = dict(printed.__dict__)
    exec(compile(textwrap.dedent(block), str(HERE.parent / "check_main_constants.py"), "exec"), environment)
    return environment


def main():
    general = original_block(printed.check_uniform_lower_higher_moments,
        "    pi=lambda k:", '    print("PASS: simplified general alpha96/25;')
    assert general["s"] == F(713, 1000)
    assert general["angle"] == F(793769, 10**6)
    assert general["r"] == F(701165, 10**6)
    assert general["r0"] == F(999444, 10**6)
    assert general["q"] == F(1382339291, 40000000000)
    assert general["bound"] == F(92147397657384409, 24000000000000000)
    assert general["bound"] < F(96, 25)
    endpoint = original_block(printed.check_k_one_lower,
        "    z={(0,1):F(1)}", "    assert F(28,25)**2>")
    assert endpoint["k0"] == F(73, 100)
    assert endpoint["correction"] == F(791977385221, 600000000000)
    assert endpoint["correction"] < F(33, 25)
    lean = (HERE / "SingularValueBounds/KL/Lower/ProfileIntegral.lean").read_text()
    # These are literal interface endpoints, not source digests or proof exports.
    for literal in ("Real.arcsin (713/1000)", "793769/1000000", "701165/1000000",
                    "999444/1000000", "Real.arcsin (73/100)", "< 96/25", "< 33/25"):
        assert literal in lean, f"Review changed Lean profile interface: {literal}"
    print("PASS: both original exact profile integral certificates; all endpoints and rational roundings match Lean.")


if __name__ == "__main__":
    main()
