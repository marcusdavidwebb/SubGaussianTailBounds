#!/usr/bin/env python3
"""Finite rational witness interface for P23 upper second moments.
Checks exactly the bounded comparisons in GeneralSecondCertificateConditions.
Analytic enclosures, monotonicity and continuous coverage are Lean proofs.
"""
if not __debug__:raise SystemExit('Run without -O: exact assertions are required.')
from fractions import Fraction as F
from math import factorial
from pathlib import Path
import hashlib
import importlib.util
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('primary',HERE.parent/'check_main_constants.py')
primary=importlib.util.module_from_spec(spec);spec.loader.exec_module(primary)
S=10**12
up=lambda x:F(-((-x.numerator*S)//x.denominator),S)
down=lambda x:F((x.numerator*S)//x.denominator,S)
def taylor(x):return sum((x**j/F(factorial(j)) for j in range(49)),F(0))
def taylor_upper(x):return taylor(x)+x**49/F(factorial(49))/(1-x/50)
def eu(x):
    assert -50<x<50
    return up(taylor_upper(x) if x>=0 else 1/taylor(-x))
def el(x):
    assert -50<x<50
    return down(taylor(x) if x>=0 else 1/taylor_upper(-x))
def log_count(x):return 3 if x>=8 else 2 if x>=4 else 1 if x>=2 else 0
def log_core(x):
    z=(x-1)/(x+1)
    return sum((2*z**(2*j+1)/F(2*j+1) for j in range(24)),F(0))
def log_lower(x):
    assert x>=1
    k=log_count(x);r=x/2**k
    assert r>=1
    # All actual witnesses also match the primary while-loop reduction exactly.
    assert r<2
    return down(log_core(r)+k*log_core(F(2)))
def cosh_lower(x):return (el(x)+el(-x))/2-1
def exclusion(m,E,x):
    assert m>0 and 0<x<50 and cosh_lower(x)>=0
    return m*log_lower(1+cosh_lower(x)/m)-E*x*x/2
ROWS=[(F(91,2000),F(947,100),F(47,50)**4+(1-F(47,50)**2)**2),
      (F(7,160),F(239,25),F(19,20)**4+(1-F(19,20)**2)**2),
      (F(19,500),F(10),F(1))]
def rarepoly(A,d):return (A+6*d)**2/2+F(50,23)*(A+6*d)+F(50,23)**2

def main():
    path=HERE/'SingularValueBounds/KL/Upper/GeneralSecondData.lean'
    digest=hashlib.sha256(path.read_bytes()).hexdigest()
    assert digest==SOURCE_DIGEST,'Review the explicit finite source/data correspondence before updating provenance.'
    assert exclusion(F(4),eu(F(1,25)),F(5,2))>F(1,100)
    assert el(F(-1,25))>=0
    for p,A,z in ROWS:
        assert 4*(1+2*z)/6+p*rarepoly(A,F(0))-el(F(-1,25))/(2*F(51,50))<F(9,2)
    margins=[]
    for j in range(334):
        yl=F(j+376,1000);yh=F(j+377,1000);dl=yl**4;dh=yh**4
        assert 0<=dl<=dh<1 and 2*dh<50
        assert eu(-2*dl)>=0 and el(-2*dh)>=0
        E=eu(2*dh)
        m=up((3+F(9,2)*yh**2-F(21,10)*yh**4-F(4,5)*yh**6)*E*(1+yh**4))
        xx=20*yh*(F(29,5)+3*yh**2)
        n=(2*xx.numerator+xx.denominator)//(2*xx.denominator)
        assert n==(xx+F(1,2)).__floor__()
        x=F(n,20)
        assert exclusion(m,E,x)>F(1,10000)
        for p,A,z in ROWS:
            bound=m*eu(-2*dl)*(1+2*z)/(6*(1+dl))+p*eu(-F(19,25)*dl)*rarepoly(A,dl)/(1+dl)-el(-2*dh)/(2*(1+dh))
            assert bound<F(9,2)
            margins.append(F(9,2)-bound)
    assert min(margins)>F(1,125) and len(margins)==1002
    assert F(376,1000)**4<F(1,50) and F(710,1000)**4>F(1,4)
    # An altered moment witness defeats the exclusion predicate.
    assert exclusion(F(2),eu(F(1,25)),F(5,2))<0
    primary.check_general_upper_second_moment()
    print(f'PASS: GeneralSecondCertificateConditions 334 cells/1002 row bounds, endpoint case, all finite domains/exclusions; source {digest}.')
SOURCE_DIGEST='04b76341a5d3aa217e6947525a649784dccf06aea107a37f43d8ca6b4b94e759'
if __name__=='__main__':main()
