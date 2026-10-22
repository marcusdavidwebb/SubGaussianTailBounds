#!/usr/bin/env python3
"""Whole-interval finite Taylor/Bernstein data for P11 plateau costs.
No analytic assertion or integral is accepted by this checker. The Lean
consequences retain explicit PlateauCostCertificateConditions hypotheses.
"""
if not __debug__:
    raise SystemExit('Run without -O: assertions are required.')
import ast
import hashlib
import importlib.util
from fractions import Fraction as F
from pathlib import Path
import sys
sys.dont_write_bytecode=True
HERE=Path(__file__).resolve().parent
spec=importlib.util.spec_from_file_location('poly',HERE/'check_polynomial_interface.py')
poly=importlib.util.module_from_spec(spec);spec.loader.exec_module(poly)
add,scale,mul,power=poly.add,poly.scale,poly.mul,poly.power
ONE={(0,0):F(1)};X={(1,0):F(1)}
def cn(q):return scale(ONE,q)
def inputs(i):
    if i==0:
        s=F(347,500);u=F(1207,1000);w=F(26,25);c=F(17,10)
        A=add(X,scale(add(ONE,cn(s*s),scale(power(X,2),-1)),F(7,10)/(2*s)))
        v=add(cn(F(1631,1000)),scale(add(A,cn(-F(6,5))),(F(167,100)-F(1631,1000))/(F(1211,1000)-F(6,5))))
        interval=F(71,100),F(147,200)
    else:
        u=F(6,5);w=F(21,20);c=F(19,10);A=cn(F(74,55));v=cn(F(27,16));interval=F(147,200),F(1)
    E=add(mul(v,add(ONE,scale(power(X,2),-1))),cn(-4+w/2),scale(X,-u/2),scale(power(X,4),w))
    d=add(ONE,scale(add(X,mul(A,power(X,2)),scale(power(X,3),-c)),-u))
    return u,w,c,A,v,E,d,interval

def main():
    source=HERE/'SingularValueBounds/KL/Lower/PlateauCostData.lean'
    digest=hashlib.sha256(source.read_bytes()).hexdigest()
    assert digest==SOURCE_DIGEST,'Review exact polynomial/source correspondence after changes.'
    counts=[]
    for i in range(2):
        u,w,c,A,v,E,d,(a,b)=inputs(i)
        C=F(4137,1000)
        assert 0<u and 0<w and 4<u*C
        minus2E=scale(E,-2);t=ONE;T=ONE
        for j in range(1,25):t=scale(mul(t,minus2E),F(1,j));T=add(T,t)
        margin=add(mul(d,T),cn(-F(400)/(9*w*w*(u*C-4)**2)))
        count=0
        for p,n in [(scale(E,-1),4),(add(d,cn(-F(1,10**6))),4),(margin,100)]:
            assert a<b and max(k for k,l in p)<=n and all(l==0 for k,l in p)
            q=poly.transformed(p,a,b,F(0),F(1));bs=poly.coefficients(q,n,0)
            poly.verify_expansion(q,n,0,bs)
            assert min(map(min,bs))>0
            count+=n+1
        counts.append(count)
    assert counts==[111,111]
    # Mutating the required bound defeats the finite Bernstein acceptance.
    bad=poly.coefficients(poly.transformed(add(margin,cn(-1000000)),a,b,F(0),F(1)),100,0)
    assert min(map(min,bad))<0
    # Re-run the primary exact certificate, preserving its distinct critical-point
    # route and every printed finite check as an independent arithmetic check.
    poly.original.check_uniform_lower_plateau()
    print(f'PASS: PlateauCostCertificateConditions, 2 ranges/6 intervals/222 coefficient signs and exact expansion identities; source {digest}.')
SOURCE_DIGEST='d665bafbc81e26ecd4c5ca26e9a6209db1c30c2ded4b76e84f54e022133651cc'
if __name__=='__main__':main()
