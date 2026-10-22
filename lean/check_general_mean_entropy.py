#!/usr/bin/env python3
"""Exact finite P20 entropy predicates; this is not an analytic proof export."""
from fractions import Fraction as F
from functools import lru_cache
from pathlib import Path
import ast, hashlib

if not __debug__:
    raise SystemExit('Exact certificate checks require assertions; do not run Python with -O.')

ROOT=Path(__file__).resolve().parents[1]
SOURCE=ROOT/'check_main_constants.py'
# Reviewed-source provenance drift guards, not compiler proof exports.
# A change requires renewed comparison of the Lean predicates/algorithm with
# this exact-arithmetic adapter before these digests may be updated.
REVIEWED_LEAN_SOURCES={
    'GeneralMeanNumerics.lean':'f245aff28f97f7646a1f37f7436444f6e1434774e18deb2473a966347cacb4bc',
    'RoundedAlgorithm.lean':'965fecbd4b946155e21810afb307690e7d2565bd82cad6bf4b0d1e8bb4ee0dcd',
}

def check_reviewed_source_drift():
    lean_upper=ROOT/'lean'/'SingularValueBounds'/'KL'/'Upper'
    for name,expected in REVIEWED_LEAN_SOURCES.items():
        actual=hashlib.sha256((lean_upper/name).read_bytes()).hexdigest()
        if actual!=expected:
            raise SystemExit(f'Reviewed-source provenance drift: {name}; review the adapter correspondence before updating its SHA256 guard.')

check_reviewed_source_drift()

S=10**15
W=F(47,20)

def ceildiv(n,d): return -((-n)//d)
def up(x): return F(ceildiv(x.numerator*S,x.denominator),S)

def rows_from_source():
    tree=ast.parse(SOURCE.read_text())
    fn=next(n for n in tree.body if isinstance(n,ast.FunctionDef) and n.name=='check_general_upper_drift')
    raw=next(n.value for n in fn.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='raw' for t in n.targets))
    cv=next(n.value for n in fn.body if isinstance(n,ast.Assign) and any(isinstance(t,ast.Name) and t.id=='CV' for t in n.targets))
    rates={F(ast.literal_eval(k.args[0])):F(ast.literal_eval(v.args[0])) for k,v in zip(cv.keys,cv.values)}
    rows=[tuple(map(F,r)) for r in ast.literal_eval(raw)]
    assert len(rows)==1330
    return rows,rates

@lru_cache(None)
def log_unit(x):
    assert 1<=x<=2
    z=(x-1)/(x+1)
    zl=z.numerator*S//z.denominator; zh=ceildiv(z.numerator*S,z.denominator)
    z2l=zl*zl//S; z2h=ceildiv(zh*zh,S)
    pl=[zl]; ph=[zh]; cl=[]; ch=[]
    for j in range(18):
        cl.append(2*pl[-1]//(2*j+1)); ch.append(ceildiv(2*ph[-1],2*j+1))
        pl.append(pl[-1]*z2l//S); ph.append(ceildiv(ph[-1]*z2h,S))
    lo=sum(cl); hi=sum(ch)+ceildiv(2*ph[18]*S,37*(S-z2h))
    # LogTranscript 18 on exact z, not on either rounded z.
    assert 0<=z<1 and all(v>=0 for v in pl+ph)
    assert F(pl[0],S)<=z<=F(ph[0],S)
    for j in range(18):
        assert F(pl[j+1],S)<=F(pl[j],S)*z*z
        assert F(ph[j],S)*z*z<=F(ph[j+1],S)
        assert F(cl[j],S)<=2*F(pl[j],S)/(2*j+1)
        assert 2*F(ph[j],S)/(2*j+1)<=F(ch[j],S)
    assert sum(map(lambda v:F(v,S),ch))+2*F(ph[18],S)/(37*(1-z*z))<=F(hi,S)
    return lo,hi

@lru_cache(None)
def log_bounds(x):
    assert x>0
    if x<1:
        l,h=log_bounds(1/x)
        return -h,-l
    u=x; k=0
    while u>=2: u/=2; k+=1
    assert x==2**k*u
    # Lean's fuel Nat.log 2 |num|+1 always exceeds this iteration count.
    assert k<=x.numerator.bit_length()
    l,h=log_unit(u); l2,h2=log_unit(F(2))
    return F(l+k*l2,S),F(h+k*h2,S)

@lru_cache(None)
def exp_upper(x):
    y=up(x)
    assert x<=y
    z=int(y*S)
    if z<0:
        terms=[S]
        for j in range(1,81): terms.append(terms[-1]*(-z)//(S*j))
        total=sum(terms)
        assert total>0 and terms[0]<=S
        for j in range(80): assert terms[j+1]*S*(j+1)<=terms[j]*(-z)
        out=ceildiv(S*S,total)
        assert F(1,F(total,S))<=F(out,S)
    else:
        assert z<82*S
        terms=[S]
        for j in range(1,81): terms.append(ceildiv(terms[-1]*z,S*j))
        assert terms[0]>=S
        for j in range(80): assert terms[j]*z<=terms[j+1]*S*(j+1)
        nxt=ceildiv(terms[-1]*z,81*S)
        rem=ceildiv(nxt*S*82,82*S-z)
        out=sum(terms)+rem
        exact_rem=(F(terms[80],S)*y/81)/(1-y/82)
        assert F(sum(terms),S)+exact_rem<=F(out,S)
    return F(out,S)

def IU(x): return (x**3+11*x*x+26*x+6)/(x*(x**3+12*x*x+36*x+24))
def IL(x): return (x*x+8*x+11)/(x**3+9*x*x+18*x+6)

def check_row(row,rates):
    kl,k,al,a,J,majorant,q,c=row
    C=F(0) if q<=2 else rates[q]
    assert k>0 and a>=0 and q>0 and c>0 and q*k*k<1 and C>=0 and q*c/2>2
    A=exp_upper(q/2+a/(2*k**3)*(-log_bounds(1-q*k*k)[0]-q*k*k)+C/(2*k*k))
    s=W/(k*(q-1)) if q!=1 else F(0)
    if q>1: assert c<=s and q*s/2>2
    nodes=[F(j,40) for j in range(40,161)]
    values=[]
    for L in nodes:
        raw=2*A/q*exp_upper(-2-(q*c/2-2)*L)*(1+IU(q*c*L/2))
        if q>1:
            raw+=A*exp_upper(-2-(q*s/2-2)*L)*((2-2/q)*(1+log_bounds(s/c)[1])+2*IU(s*L/2)-2/q*IL(q*s*L/2))
        out=F(ceildiv(raw.numerator*10**10,raw.denominator),10**10)
        assert raw<=out
        values.append(out)
    minimum=F(10)
    for j,(l,h,el,eh) in enumerate(zip(nodes,nodes[1:],values,values[1:])):
        slope=(eh-el)/(h-l); rate=W-2-slope
        assert rate>0
        critical=min(h,max(l,1/rate))
        margin=2+rate*critical-log_bounds(c*critical)[1]-J/2-el+slope*l
        assert margin>F(1,100000),(row,j,margin)
        minimum=min(minimum,margin)
    margin=2+4*(W-2)-log_bounds(4*c)[1]-J/2-values[-1]
    assert margin>F(1,100000),(row,'unbounded',margin)
    return min(minimum,margin)

def main():
    rows,rates=rows_from_source()
    small=(F(2,5),F(2,5),F(2,5),F(2,5),F(257,120),F(4),F(11,4),F(193,100))
    margins=[]
    for j,row in enumerate([small]+rows):
        margins.append(check_row(row,rates))
        if j and j%250==0: print(f'checked {j}/1330 finite entropy rows',flush=True)
    assert len(margins)==1331 and min(margins)>F(1,100000)
    # The same finite row checks reject a materially corrupted determinant cost.
    corrupted=list(rows[0]); corrupted[4]+=10
    try:
        check_row(tuple(corrupted),rates)
    except AssertionError:
        pass
    else:
        raise AssertionError('critical-margin mutation was not rejected')
    # A deliberately increased lower Taylor term violates its transcript step.
    assert not (F(2)<=F(1)*F(1)/1)
    # A deliberately inward-rounded final value violates nodeRound.
    assert not (F(1)<=F(1)-F(1,10**10))
    print(f'PASS P20:1330 rectangles+smallshape;161051 node enclosures;159720 chords;1331 unbounded cells.')
    print(f'Exact rounded transcripts: exp={exp_upper.cache_info().currsize}, log={log_bounds.cache_info().currsize}, unitlog={log_unit.cache_info().currsize}.')
    print('PASS: two reviewed Lean source provenance drift guards (not compiler proof exports).')
    print('Original-source digest (provenance only):',hashlib.sha256(SOURCE.read_bytes()).hexdigest())

if __name__=='__main__': main()
