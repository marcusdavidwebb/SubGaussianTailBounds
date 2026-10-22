#!/usr/bin/env python3
"""Exact arithmetic certificates for the supplementary proof accompanying main.tex.

The stated choices are (alpha,beta,gamma,delta)=(3.84,1.58,2.35,1.5),
and (1.32,1.12,2.32,sqrt(2)) when K=1.
This script checks the finite polynomial identities,
Bernstein coefficients, and rational/Taylor
inequalities displayed in the supplement. It uses Python's standard
library and exact fractions throughout; no numerical libraries, data
files, or /tmp dependencies are required at runtime.

This is NOT a formal verification of the probabilistic or matrix proof.
The analytic arguments, hypotheses, and correspondence with main.tex
must still be reviewed; a future Lean development will have a wider scope.
Run normally (not with Python's -O flag, which disables assertions).
"""
if not __debug__:
    raise SystemExit("Run without -O: this checker requires assertions.")

from fractions import Fraction as F
from math import comb, factorial

# Bivariate polynomials are dictionaries (a_degree, x_degree) -> Fraction.
# Missing powers have coefficient zero. All comparisons below are exact;
# floating-point approximations are deliberately excluded from certificates.

def add(*ps):
 out={}
 for p in ps:
  for i,c in p.items():out[i]=out.get(i,F(0))+c
 return {i:c for i,c in out.items() if c}
def scale(p,c):return {i:x*c for i,x in p.items() if x*c}
def mul(p,q):
 out={}
 for (a,r),x in p.items():
  for (b,s),y in q.items():out[a+b,r+s]=out.get((a+b,r+s),F(0))+x*y
 return {i:c for i,c in out.items() if c}
def ppow(p,n):
 out={(0,0):F(1)}
 for _ in range(n):out=mul(out,p)
 return out
one={(0,0):F(1)}

def bern(poly,al,ah,rl,rh):
 """Smallest tensor-product Bernstein coefficient on the given rectangle."""
 na=max(a for a,r in poly);nr=max(r for a,r in poly)
 pol={}
 for (a,r),v in poly.items():
  for i in range(a+1):
   for j in range(r+1):
    pol[i,j]=pol.get((i,j),F(0))+v*comb(a,i)*al**(a-i)*(ah-al)**i*comb(r,j)*rl**(r-j)*(rh-rl)**j
 out=[]
 for i in range(na+1):
  for j in range(nr+1):
   out.append(sum(v*F(comb(i,a),comb(na,a))*F(comb(j,r),comb(nr,r)) for (a,r),v in pol.items() if a<=i and r<=j))
 return min(out)


def check_k_one_lower():
    """Two-row certificate for cap73/50 and the rounded K=1 lower constants."""
    def cn(c):return scale(one,F(c))
    k={(1,0):F(1)};r={(0,1):F(1)}
    A0=F(73,55);c0=F(103,55);cap=F(73,50)
    def poly(theta,xi,chi,omega):
     A=add(scale(k,theta),cn((1-theta)*A0));c=theta+(1-theta)*c0
     gco=[add(scale(A,1/xi),cn(1-c)),add(A,cn(xi/2-c/xi),scale(ppow(A,2),1/(2*xi))),add(cn(-c),scale(A,-c/xi)),cn(c*c/(2*xi))]
     nco=[add(scale(A,2/chi),cn(-c)),add(cn(chi-2*c/chi),scale(ppow(A,2),1/chi)),scale(A,-2*c/chi),cn(c*c/chi)]
     def g(cs,x):return add(*(mul(ci,ppow(x,i+1))for i,ci in enumerate(cs)))
     w=add(one,scale(ppow(k,2),-1));d=mul(k,add(one,mul(A,k),scale(ppow(k,2),-c)))
     O=add(A,cn(1/(2*xi)),mul(ppow(k,2),g(gco,k)),mul(w,g(gco,r)))
     N=add(A,scale(ppow(k,3),-c),scale(mul(ppow(k,2),d),2),scale(w,1/chi),mul(w,g(nco,r)))
     return add(cn(cap),scale(O,-omega),scale(N,omega-1))
    rows=[(F(73,100),F(3,4),F(9,20),F(8,5),F(2),F(3,10)),(F(3,4),F(7,9),F(1,4),F(8,5),F(12,5),F(9,20))]
    count=0
    for kl,kh,theta,xi,chi,omega in rows:
     P=poly(theta,xi,chi,omega)
     assert max(i for i,j in P)==6 and max(j for i,j in P)==4
     for j in range(4):
      assert bern(P,kl,kh,F(7*j,40),F(7*(j+1),40))>F(1,5000)
      count+=35
    assert count==280
    # Tangent, positivity, block-norm and covariance-ratio hypotheses.
    assert A0*A0==1+(c0-1)**2<c0
    assert 1+A0-c0>0
    assert 1+(A0-1)*F(4,5)-c0*F(4,5)**2>0
    assert F(25,16)*(1-F(73,100)**2)<F(36,49)
    assert F(40,7)+F(7,40)==F(1649,280)<6
    # Small remaining Frobenius norm, where B0 suffices.
    kh=F(7,9);p=F(3,20)
    assert cap-kh-kh*p*p>0
    assert (cap-kh-kh*p*p)**2-(kh**4+p*p)*(1+p-p*p)==F(407087,104976000)>0
    # Far-concentrated spectra: one quartic and its derivative.
    coeff=[F(0),F(1,32),F(1849,1280),-F(399,128),F(245,256)]
    g={(0,j):v for j,v in enumerate(coeff)if v}
    gap=add(cn(F(7,100)),scale(g,-1))
    knots=[F(0),F(1,4),F(3,8),F(1,2),F(1)]
    for lo,hi in zip(knots,knots[1:]):assert bern(gap,F(0),F(1),lo,hi)>0
    neg_der={(0,0):F(7,50),**{(0,j):-(j+2)*coeff[j]for j in range(1,5)}}
    assert bern(neg_der,F(0),F(1),F(3,4),F(1))>0
    assert F(5,4)**2==1+(F(7,4)-1)**2 and 1+F(5,4)-F(7,4)>0
    far=F(25,16)+kh*kh*sum(v*kh**j for j,v in enumerate(coeff))+(1-kh*kh)*F(7,100)
    assert far==F(77489969,53144100)<cap
    # Correction integral and rounded fluctuation coefficient.
    z={(0,1):F(1)}
    sq=add(one,scale(z,-F(1,2)),scale(ppow(z,2),-F(1,8)))
    assert add(ppow(sq,2),scale(one,-1),z)==add(scale(ppow(z,3),F(1,8)),scale(ppow(z,4),F(1,64)))
    k0=F(73,100)
    assert k0*k0<F(4,5)
    correction=2*(k0-k0**3/6-k0**5/40)
    assert correction==F(791977385221,600000000000)<F(33,25)
    assert F(28,25)**2>F(5,4)
    print('PASS: simplified K=1 lower constants alpha=1.32,beta=1.12;280 Bernstein coefficients.')


def check_determinants():
    """All six common scalar majorants, using one deterministic subdivision rule."""
    # Existing H_j,D,N polynomials.
    one={(0,0):F(1)};a={(1,0):F(1)};x={(0,1):F(1)}
    z=scale(add(x,mul(a,ppow(x,2)),scale(ppow(x,3),-2)),2)
    DP=add(one,scale(z,F(-16,7)),scale(ppow(z,2),F(12,7)),scale(ppow(z,3),F(-16,35)),scale(ppow(z,4),F(1,35)))
    NP=add(z,scale(ppow(z,2),F(-25,14)),scale(ppow(z,3),F(19,21)),scale(ppow(z,4),F(-47,420)))
    Bs=[{(0,0):F(13,6)},add({(0,0):F(13,6)},scale(ppow(add(a,{(0,0):F(-1,4)}),2),-4)),{(0,0):F(13,5)}]
    As=[add(one,scale(a,9)),add(scale(a,20),{(0,0):F(-2)}),add(scale(a,24),{(0,0):F(-22,3)})]
    Hs=[add(scale(x,2),mul(B,ppow(x,2)),scale(mul(mul(A,ppow(x,2)),add(x,scale(a,-1))),-1))for B,A in zip(Bs,As)]
    tt=add(a,scale(one,-F(7,20)))
    B6=add(scale(one,F(258,125)+F(1,1000)),scale(tt,-F(1339,1000)),scale(ppow(tt,2),-F(10009,1000)),scale(ppow(tt,3),-F(25197,1000)))
    A6=add(scale(one,F(816,125)),scale(tt,F(7307,200)),scale(ppow(tt,2),F(9971,100)),scale(ppow(tt,3),F(18903,250)))
    H6=add(scale(x,2),mul(B6,ppow(x,2)),scale(mul(mul(A6,ppow(x,2)),add(x,scale(a,-1))),-1))
    Jnorm=add(scale(a,-2),scale(add(one,scale(ppow(a,2),-1),scale(mul(ppow(a,2),ppow(add(one,scale(a,-1)),2)),-1)),F(671,100)))

    Hs=Hs+[add(Hs[1],scale(ppow(x,2),-F(1,30))),add(Hs[0],scale(ppow(x,2),-F(1,40))),H6]
    domains=[(F(0),F(27,40),F(0),F(1)),(F(1,4),F(37,50),F(0),F(1)),(F(7,10),F(5,6),F(0),F(1)),(F(1,4),F(7,10),F(0),F(1)),(F(0),F(13,20),F(0),F(1)),(F(1,4),F(51,100),F(0),F(13,20))]
    for i,(H,domain) in enumerate(zip(Hs,domains),1):
        p=add(mul(H,DP),scale(NP,-1));assert all(xd>=2 for ad,xd in p)
        Q={(ad,xd-2):v for (ad,xd),v in p.items()}
        counts=[0,0];mins=[]
        def rec(box,depth):
            v=bern(Q,*box)
            if v>0:
                counts[0]+=1;counts[1]=max(counts[1],depth);mins.append(v);return
            assert depth<5,(i,box,v)
            al,ah,xl,xh=box;am=(al+ah)/2;xm=(xl+xh)/2
            for aa,bb in[(al,am),(am,ah)]:
                for xx,yy in[(xl,xm),(xm,xh)]:rec((aa,bb,xx,yy),depth+1)
        rec(domain,0)
        assert counts[0]==[19,19,13,28,16,70][i-1]
        assert min(mins)>F(1,100000)

    def deriv(p):return {(a,r-1):v*r for (a,r),v in p.items() if r}
    z={(0,1):F(1)}
    Dz=add(one,scale(z,-F(16,7)),scale(ppow(z,2),F(12,7)),scale(ppow(z,3),-F(16,35)),scale(ppow(z,4),F(1,35)))
    Nz=add(z,scale(ppow(z,2),-F(25,14)),scale(ppow(z,3),F(19,21)),scale(ppow(z,4),-F(47,420)))
    assert add(mul(add(one,scale(z,-1)),add(mul(deriv(Nz),Dz),scale(mul(Nz,deriv(Dz)),-1))),scale(ppow(Dz,2),-1))==scale(mul(add(one,scale(z,-1)),ppow(z,7)),F(1,1225))
    assert F(56,25)**2>5
    assert (25+11*F(56,25))/250<F(223,500)**2
    exponent=2*F(223,500)+F(671,100)*F(223,500)**2
    assert sum(exponent**j/factorial(j) for j in range(9))>F(250,27)
    print('PASS: six common determinant majorants;165 rectangles, depth<=5, margin>1e-5.')


def check_k_one_upper_entropy():
    """Exact finite certificates for the K=1 upper drift cap 58/25."""
    S=10**15;NU=200;END=40*NU;NQ=100;W=F(58,25);TARGET=F(58,25)
    def ceildiv(n,d):return (n+d-1)//d
    def ceilF(x):return ceildiv(x.numerator,x.denominator)

    def _log_unit(n,d):
     zn=n-d;zd=n+d;zl=zn*S//zd;zh=ceildiv(zn*S,zd)
     z2l=zl*zl//S;z2h=ceildiv(zh*zh,S);tl=zl;th=zh;lo=0;hi=0
     for j in range(18):
      lo+=2*tl//(2*j+1);hi+=ceildiv(2*th,2*j+1)
      tl=tl*z2l//S;th=ceildiv(th*z2h,S)
     hi+=ceildiv(2*th*S,37*(S-z2h))
     return lo,hi
    L2=_log_unit(2,1)
    def logi(n,d=1):
     assert n>0 and d>0
     if n<d:
      l,h=logi(d,n);return -h,-l
     k=0
     while n>=2*d:d*=2;k+=1
     l,h=_log_unit(n,d);return l+k*L2[0],h+k*L2[1]
    def expi(z):
     N=80
     if z<0:
      z=-z;term=S;total=S
      for j in range(1,N+1):term=term*z//(S*j);total+=term
      return ceildiv(S*S,total)
     term=S;total=S
     for j in range(1,N+1):term=ceildiv(term*z,S*j);total+=term
     nxt=ceildiv(term*z,S*(N+1));den=S*(N+2)-z;assert den>0
     return total+ceildiv(nxt*S*(N+2),den)
    logs=[(0,0)]+[logi(j,NU)for j in range(1,END+2)]
    exps=[]
    for qi in range(90,201):
     base=expi(-((qi*S)//(NQ*2*NU)));v=S;arr=[v]
     for j in range(END+1):v=ceildiv(v*base,S);arr.append(v)
     exps.append(arr)

    def pref(k,a,qi):
     kn,kd=k.numerator,k.denominator;an,ad=a.numerator,a.denominator
     d=NQ*kd*kd;n=d-qi*kn*kn
     if n<=0:return None
     l,h=logi(n,d)
     J=-l-(qi*kn*kn*S//d)
     logA=ceildiv(qi*S,2*NQ)+ceildiv(an*kd**3*J,2*ad*kn**3)
     return expi(logA)

    def entropy_corners(kl,kh,al,ah):
     k=(kl+kh)/2;a=(al+ah)/2
     if k<=F(1,2):cc=F(43,20)+F(6,5)*k*k+F(9,2)*k**4
     else:
      x=k-F(1,2);cc=F(273,100)+F(37,10)*x+17*x*x-11*x**3
     cc-=(2*k+F(1,4))*(k-a)
     j0=ceilF(cc*NU);c=F(j0,NU)
     corners=[(kl,al),(kl,ah),(kh,al),(kh,ah)]
     As=[[pref(kk,aa,qi)for qi in range(90,201)]for kk,aa in corners]
     sums=[0]*4
     kn,kd=k.numerator,k.denominator;an,ad=a.numerator,a.denominator;hn,hd=kh.numerator,kh.denominator
     spect=ceildiv(NQ*hd*hd,hn*hn)-1
     for j in range(j0,END):
      oi=NQ*(j-NU)*kd*kd*ad//(kn*an*kd*NU+kn*kn*ad*(j-NU))
      ci=NQ+(NQ*W.numerator*NU*hd)//(W.denominator*j*hn)
      qi=max(90,min(200,oi,ci,spect));idx=qi-90
      zz=(S+logs[j+1][1]-logs[j0][0])*exps[idx][j]
      for h in range(4):
       assert As[h][idx] is not None
       # exact product is an upper bound; no rescaling needed here
       sums[h]+=zz*As[h][idx]
     r=F(9,20);tail=F(31623,10000)*F(exps[0][END],S)*(1/r+40/(c*r)+1/(c*r*r))
     Ds=[]
     for su in sums:
      D=F(logs[j0][1],S)+F(su,NU*S**3)+tail
      Ds.append(F(ceilF(D*10**9),10**9))
     return Ds,c

    # Existing H_j,D,N polynomials.
    one={(0,0):F(1)};a={(1,0):F(1)};x={(0,1):F(1)}
    z=scale(add(x,mul(a,ppow(x,2)),scale(ppow(x,3),-2)),2)
    DP=add(one,scale(z,F(-16,7)),scale(ppow(z,2),F(12,7)),scale(ppow(z,3),F(-16,35)),scale(ppow(z,4),F(1,35)))
    NP=add(z,scale(ppow(z,2),F(-25,14)),scale(ppow(z,3),F(19,21)),scale(ppow(z,4),F(-47,420)))
    Bs=[{(0,0):F(13,6)},add({(0,0):F(13,6)},scale(ppow(add(a,{(0,0):F(-1,4)}),2),-4)),{(0,0):F(13,5)}]
    As=[add(one,scale(a,9)),add(scale(a,20),{(0,0):F(-2)}),add(scale(a,24),{(0,0):F(-22,3)})]
    Hs=[add(scale(x,2),mul(B,ppow(x,2)),scale(mul(mul(A,ppow(x,2)),add(x,scale(a,-1))),-1))for B,A in zip(Bs,As)]
    tt=add(a,scale(one,-F(7,20)))
    B6=add(scale(one,F(258,125)+F(1,1000)),scale(tt,-F(1339,1000)),scale(ppow(tt,2),-F(10009,1000)),scale(ppow(tt,3),-F(25197,1000)))
    A6=add(scale(one,F(816,125)),scale(tt,F(7307,200)),scale(ppow(tt,2),F(9971,100)),scale(ppow(tt,3),F(18903,250)))
    H6=add(scale(x,2),mul(B6,ppow(x,2)),scale(mul(mul(A6,ppow(x,2)),add(x,scale(a,-1))),-1))
    Jnorm=add(scale(a,-2),scale(add(one,scale(ppow(a,2),-1),scale(mul(ppow(a,2),ppow(add(one,scale(a,-1)),2)),-1)),F(671,100)))

    def bilinear(kl,kh,al,ah,Ds):
     # D00 (klo,alo),D01 (klo,ahi),D10 (khi,alo),D11 (khi,ahi)
     ac=(Ds[1]-Ds[0])/(ah-al);kc=(Ds[2]-Ds[0])/(kh-kl);cross=(Ds[3]-Ds[2]-Ds[1]+Ds[0])/((ah-al)*(kh-kl))
     return {(0,0):Ds[0]-ac*al-kc*kl+cross*al*kl,(1,0):ac-cross*kl,(0,1):kc-cross*al,(1,1):cross}

    def certify(kl,kh,al,ah,Ds):
     DD=bilinear(kl,kh,al,ah,Ds);base=add(scale(one,TARGET),scale(DD,-1))
     choices=[]
     if ah<=F(27,40):choices.append(0)
     if al>=F(1,4)and ah<=F(37,50):choices.append(1)
     if al>=F(7,10)and ah<=F(5,6):choices.append(2)
     if al>=F(5,6):choices.append(3)
     if al>=F(1,4) and ah<=F(7,10):choices.insert(0,4)
     if ah<=F(13,20):choices.append(5)
     if al>=F(1,4) and ah<=F(9,20) and kh<=F(13,20):choices.append(6)
     best=None
     for j in choices:
      if j==6:P=add(mul(add(base,scale(B6,F(-1,2)),scale(H6,F(1,2))),DP),scale(NP,F(-1,2)))
      elif j==5:P=add(mul(add(base,scale(Bs[0],F(-1,2)),scale(Hs[0],F(1,2)),scale(add(one,scale(ppow(x,2),-1)),F(1,80))),DP),scale(NP,F(-1,2)))
      elif j==4:P=add(mul(add(base,scale(Bs[1],F(-1,2)),scale(Hs[1],F(1,2)),scale(add(one,scale(ppow(x,2),-1)),F(1,60))),DP),scale(NP,F(-1,2)))
      elif j==3:P=add(base,scale(Jnorm,F(-1,2)))
      else:P=add(mul(add(base,scale(Bs[j],F(-1,2)),scale(Hs[j],F(1,2))),DP),scale(NP,F(-1,2)))
      bb=bern(P,al,ah,kl,kh)
      if best is None or bb>best[0]:best=bb,j
      if bb>0:return best
     return best


    # Low-shape entropy bound on fifty intervals; reuse the exact tail arrays.
    for i in range(50):
     kl=F(i,200);kh=F(i+1,200)
     c=F(ceilF(200*(F(43,20)+F(23,10)*kh*kh)),200)
     j0=int(c*200);prefactors=[]
     for qi in range(90,201,5):
      q=F(qi,100)
      l,h=logi((1-q*kh*kh).numerator,(1-q*kh*kh).denominator)
      A=expi(ceilF(F(-l,1)/(2*kh*kh)))
      maxj=8000 if qi<=100 else (200*W/(kh*(q-1))).__floor__()
      prefactors.append((qi-90,A,maxj))
     total=0
     for j in range(j0,8000):
      p=S
      for qi,A,mj in prefactors:
       if j<=mj:p=min(p,ceildiv(A*exps[qi][j],S))
      total+=(S+logs[j+1][1]-logs[j0][0])*p
     r=F(9,20)
     tail=F(31623,10000)*F(exps[0][END],S)*(1/r+40/(c*r)+1/(c*r*r))
     bound=F(logs[j0][1],S)+F(total,200*S*S)+tail
     d1=F(239,200)+F(9,20)*kl*kl+kl**4/2
     assert d1-bound>F(1,500)
    assert F(239,200)+F(9,20)*F(1,4)**2+F(1,4)**4/2+F(13,12)-F(1,80)<W

    # Joint certificate: clip using a>=k^3; all initial rectangles pass directly.
    count=0;initial=0
    def check_box(kl,kh,al,ah):
     nonlocal count
     Ds,c=entropy_corners(kl,kh,al,ah);result=certify(kl,kh,al,ah,Ds)
     assert result is not None and result[0]>0,(kl,kh,al,ah,result)
     count+=1
    apoints=sorted(set([F(i,40) for i in range(41)]+[F(37,50),F(5,6)]))
    for ki in range(20,80):
     kl=F(ki,80);kh=F(ki+1,80)
     for al,ah in zip(apoints,apoints[1:]):
      if ah<kl**3 or al>kh:continue
      al=max(al,kl**3)
      if al>=ah:continue
      initial+=1;check_box(kl,kh,al,ah)
    assert initial==count==837
    print('PASS: K=1 gamma=58/25;1/200 integration mesh,50 small-shape cells,837 joint rectangles.')


def check_k_one_upper_mgf():
    """Certify nu=4 for K=1 under any upper drift cap at least23/10."""
    def taylor(x):return sum((x**j/F(factorial(j)) for j in range(25)),F(0))
    v=F(225,256);cut=F(13,2);s=F(2);eps=F(5,21)
    assert 1/(v*(1-v))<F(46,15)**2
    assert taylor(F(13,4))>F(644,25)
    def low(p):return (1-eps)*cut**(p-1)/factorial(p)+eps*sum((cut**j*s**(p-1-j)/factorial(j) for j in range(p)),F(0))
    assert low(2)==F(9,2)
    assert low(3)<16 and low(4)<64 and s+cut/4<4
    # Monotonicity of J((12/5)(x+a*x^2-2*x^3))/x^2.
    one={(0,0):F(1)};a={(1,0):F(1)};x={(0,1):F(1)}
    z=scale(add(x,mul(a,ppow(x,2)),scale(ppow(x,3),-2)),F(12,5))
    D=add(one,scale(z,F(-16,7)),scale(ppow(z,2),F(12,7)),scale(ppow(z,3),F(-16,35)),scale(ppow(z,4),F(1,35)))
    N=add(z,scale(ppow(z,2),F(-25,14)),scale(ppow(z,3),F(19,21)),scale(ppow(z,4),F(-47,420)))
    zd={(i,j-1):v*j for(i,j),v in z.items() if j}
    P=add(mul(mul(mul(x,zd),z),D),scale(mul(add(N,scale(mul(z,D),-1)),add(one,scale(z,-1))),-2))
    assert all(j>=3 for i,j in P)
    P={(i,j-3):v for(i,j),v in P.items()}
    assert bern(P,F(1,2),F(1),F(0),F(7,20))>F(49,500)
    assert F(12,5)*(F(7,20)+F(7,20)**2-2*F(7,20)**3)<1
    # Bounds on largest and remaining eigenvalues of C/eta.
    kl=F(15,16);kh=F(47,50);ep=1-kl*kl;r=F(87,250);rp=F(171,500)
    assert r*r>ep and rp*rp>1-kh*kh
    aa=kh**3+(1-kh*kh)*rp
    ct=kh*ep*ep+kh*kh*ep*r
    cr=r+aa*r*r-2*r**3
    assert ct<F(13,250) and cr<F(37,100)
    assert F(1,2)<aa<1 and r<F(7,20)
    assert F(23,10)+kl**3>F(31239,10000)
    kl=F(47,50);kh=F(19,20);ep=1-kl*kl;r=F(171,500);rp=F(5,16);aa=F(111,125)
    assert r*r>ep and rp*rp>1-kh*kh
    assert kh**3+(1-kh*kh)*rp<aa
    ct=kh*ep*ep+kh*kh*ep*r
    cr=r+aa*r*r-2*r**3
    assert ct<F(1,20) and cr<F(183,500)
    assert F(23,10)+kl**3>F(313,100)
    ep=F(39,400);r=F(5,16)
    assert ep<r*r
    assert ep*ep+ep*r<F(1,25)
    assert r+r*r-2*r**3<F(7,20)
    assert F(23,10)+F(19,20)**3>F(63,20)
    # Each row: c_top,c_rest,log_top,log_rest,gap,p0,tailcut,kappa_hi.
    rows=[
        (F(13,250),F(37,100),F(67,500),F(219,100),F(31239,10000),F(91,2000),F(947,100),F(47,50)),
        (F(1,20),F(183,500),F(16,125),F(527,250),F(313,100),F(7,160),F(239,25),F(19,20)),
        (F(1,25),F(7,20),F(101,1000),F(1833,1000),F(63,20),F(19,500),F(10),F(1)),
    ]
    th=F(6,5);st=F(50,23);pref=F(177,50)
    assert pref*pref>F(25,2)
    for ct,cr,lt,lr,gap,p0,cut,kh in rows:
        assert taylor(lt)>1/(1-2*th*ct)
        assert taylor(lr)>1/(1-2*th*cr)
        bound=(lt+lr-2*th*(ct+cr))/2
        assert taylor(th*gap-bound)>1/p0
        assert taylor(cut/st)>pref/p0
        zz=kh**4+(1-kh*kh)**2
        def u(p):
            gg=F(1,2)+zz if p==2 else F(comb(2*p,p),2**p)
            return gg+p0*sum((cut**j*st**(p-j)/factorial(j) for j in range(p+1)),F(0))
        assert u(2)<F(9,2)
        for p in [3,4,5]:assert u(p)<F(4)**(p-1)
        assert st+cut/6<4


    print('PASS: K=1 upper MGF coefficients, nu=4 and delta=sqrt(2).')


def check_general_upper_tail_extension():
    """Exact polynomial certificates for all fifteen upper-tail rates."""
    from fractions import Fraction as F
    from math import comb
    def add(*ps):
     r=[F(0)]*max(map(len,ps))
     for p in ps:
      for i,c in enumerate(p):r[i]+=c
     while len(r)>1 and r[-1]==0:r.pop()
     return r

    def scale(p,c):return [c*v for v in p]
    def mul(p,q):
     r=[F(0)]*(len(p)+len(q)-1)
     for i,a in enumerate(p):
      for j,b in enumerate(q):r[i+j]+=a*b
     return r

    def power(p,n):
     r=[F(1)]
     for _ in range(n):r=mul(r,p)
     return r

    def bern(p,l,h):
     n=len(p)-1
     t=[sum(p[j]*comb(j,i)*l**(j-i)*(h-l)**i for j in range(i,n+1))for i in range(n+1)]
     return min(sum(t[j]*F(comb(i,j),comb(n,j))for j in range(i+1))for i in range(n+1))

    def q_extension_poly(v,c):
     # y=theta-1 in[0,v-1], z=vy/(2y²+vy+2v-2).
     V=[F(0),v];W=[2*v-2,v,F(2)];D=add(power(W,2),scale(power(V,2),-1))
     A=[v-1,v-1]
     first=mul(add(scale(A,c),V),mul(power(W,11),D))
     series=add(*[scale(mul(mul(power(V,2*j+1),power(W,10-2*j)),D),F(1,2*j+1))for j in range(6)],scale(power(V,13),F(1,13)))
     return add(first,scale(mul(A,series),-2))

    def check_rows():
     rows=[(F(81,40),F(61,50000000)),(F(83,40),F(57,2000000)),(F(17,8),F(29,250000)),(F(41,20),F(1,100000)),(F(21,10),F(13,200000)),(F(43,20),F(19,100000)),(F(11,5),F(1,2500)),(F(23,10),F(27,25000)),(F(12,5),F(21,10000)),(F(9,4),F(7,10000)),(F(5,2),F(7,2000)),(F(11,4),F(79,10000)),(F(3),F(27,2000)),(F(7,2),F(131,5000)),(F(4),F(201,5000))]
     for v,c in rows:
      p=q_extension_poly(v,c);done=[]
      def rec(l,h,d):
       m=bern(p,l,h)
       if m>0:done.append((l,h,m));return
       assert d>0,(v,l,h,m)
       mid=(l+h)/2
       rec(l,mid,d-1);rec(mid,h,d-1)
      rec(F(0),v-1,8)
      assert len(p)==28
     return len(rows)
    count=check_rows()
    assert count==15
    print("PASS: fifteen general upper-tail extension constants.")

def check_general_I_cubic():
    """Exact identities for the cubic rational entropy-integral bounds."""
    from fractions import Fraction as F
    from math import factorial
    def add(*ps):
        out={}
        for p in ps:
            for i,c in p.items():out[i]=out.get(i,F(0))+c
        return {i:c for i,c in out.items() if c}
    def scale(p,c):return {i:v*c for i,v in p.items() if v*c}
    def mul(p,q):
        out={}
        for (i,j),a in p.items():
            for (k,l),b in q.items():out[i+k,j+l]=out.get((i+k,j+l),F(0))+a*b
        return {i:c for i,c in out.items() if c}
    def expect(p,shift=0):
        out={}
        for (i,j),c in p.items():out[i,0]=out.get((i,0),F(0))+c*factorial(j+shift)
        return {i:c for i,c in out.items() if c}
    xu={(1,0):F(1),(0,1):F(1)}
    rows=[(0,[6,18,9,1],{(2,0):1,(1,0):9,(0,0):18,(1,1):-1,(0,1):-9,(0,2):1},[-6,18,-9,1],[11,8,1]),
          (1,[24,36,12,1],{(2,0):1,(1,0):12,(0,0):36,(1,1):-1,(0,1):-12,(0,2):1},[-24,36,-12,1],[18,10,1])]
    for shift,d,p,r,n in rows:
        D={(i,0):F(c)for i,c in enumerate(d)};P={i:F(c)for i,c in p.items()};R={(0,j):F(c)for j,c in enumerate(r)};N={(i,0):F(c)for i,c in enumerate(n)}
        assert add(D,scale(mul(xu,P),-1))==scale(R,-1)
        for j in range(3):assert sum(F(c)*factorial(i+j+shift)for i,c in enumerate(r))==0
        assert expect(P,shift)==N
        assert expect(mul(xu,mul(P,P)),shift)==mul(N,D)
    print('PASS: cubic I(x) bounds and exact square-remainder identities.')


def check_general_upper_drift():
    """Exact certificates for gamma=47/20 for every K>=1."""
    from math import comb,factorial
    S=10**15;W=F(47,20)
    def ceildiv(n,d):return (n+d-1)//d
    def ceilF(x):return ceildiv(x.numerator,x.denominator)

    def _log_unit(n,d):
     zn=n-d;zd=n+d;zl=zn*S//zd;zh=ceildiv(zn*S,zd)
     z2l=zl*zl//S;z2h=ceildiv(zh*zh,S);tl=zl;th=zh;lo=0;hi=0
     for j in range(18):
      lo+=2*tl//(2*j+1);hi+=ceildiv(2*th,2*j+1)
      tl=tl*z2l//S;th=ceildiv(th*z2h,S)
     hi+=ceildiv(2*th*S,37*(S-z2h))
     return lo,hi
    L2=_log_unit(2,1)
    def logi(n,d=1):
     assert n>0 and d>0
     if n<d:
      l,h=logi(d,n);return -h,-l
     k=0
     while n>=2*d:d*=2;k+=1
     l,h=_log_unit(n,d);return l+k*L2[0],h+k*L2[1]
    def expi(z):
     N=80
     if z<0:
      z=-z;term=S;total=S
      for j in range(1,N+1):term=term*z//(S*j);total+=term
      return ceildiv(S*S,total)
     term=S;total=S
     for j in range(1,N+1):term=ceildiv(term*z,S*j);total+=term
     nxt=ceildiv(term*z,S*(N+1));den=S*(N+2)-z;assert den>0
     return total+ceildiv(nxt*S*(N+2),den)
    one={(0,0):F(1)};a={(1,0):F(1)};x={(0,1):F(1)}
    z=scale(add(x,mul(a,ppow(x,2)),scale(ppow(x,3),-2)),2)
    D=add(one,scale(z,F(-16,7)),scale(ppow(z,2),F(12,7)),scale(ppow(z,3),F(-16,35)),scale(ppow(z,4),F(1,35)))
    N=add(z,scale(ppow(z,2),F(-25,14)),scale(ppow(z,3),F(19,21)),scale(ppow(z,4),F(-47,420)))
    t=add(a,scale(one,-F(1,4)))
    Bs=[scale(one,F(13,6)),add(scale(one,F(13,6)),scale(ppow(t,2),-4)),scale(one,F(13,5))]
    As=[add(one,scale(a,9)),add(scale(a,20),scale(one,-2)),add(scale(a,24),scale(one,-F(22,3)))]
    Hs=[add(scale(x,2),mul(b,ppow(x,2)),scale(mul(mul(aa,ppow(x,2)),add(x,scale(a,-1))),-1))for b,aa in zip(Bs,As)]
    Bs+= [add(Bs[1],scale(one,-F(1,30))),add(Bs[0],scale(one,-F(1,40)))]
    Hs+= [add(Hs[1],scale(ppow(x,2),-F(1,30))),add(Hs[0],scale(ppow(x,2),-F(1,40)))]
    t=add(a,scale(one,-F(7,20)))
    B=add(scale(one,F(413,200)),scale(t,-F(1339,1000)),scale(ppow(t,2),-F(10009,1000)),scale(ppow(t,3),-F(25197,1000)))
    A=add(scale(one,F(816,125)),scale(t,F(7307,200)),scale(ppow(t,2),F(9971,100)),scale(ppow(t,3),F(18903,250)))
    Bs.append(B);Hs.append(add(scale(x,2),mul(B,ppow(x,2)),scale(mul(mul(A,ppow(x,2)),add(x,scale(a,-1))),-1)))
    Jnorm=add(scale(a,-2),scale(add(one,scale(ppow(a,2),-1),scale(mul(ppow(a,2),ppow(add(one,scale(a,-1)),2)),-1)),F(671,100)))

    CV={F('81/40'):F('61/50000000'),F('83/40'):F('57/2000000'),F('17/8'):F('29/250000'),F('9/4'):F('7/10000'),F('5/2'):F('7/2000'),F('11/4'):F('79/10000'),F('3'):F('27/2000'),F('7/2'):F('131/5000'),F('4'):F('201/5000'),F('41/20'):F('1/100000'),F('21/10'):F('13/200000'),F('43/20'):F('19/100000'),F('11/5'):F('1/2500'),F('23/10'):F('27/25000'),F('12/5'):F('21/10000')}
    Jnormhigh=add(scale(a,-2),scale(add(one,scale(ppow(a,2),-1),scale(mul(ppow(a,2),ppow(add(one,scale(a,-1)),2)),-1)),F(563,100)))
    PS=[add(mul(add(B,scale(H,-1)),D),N)for B,H in zip(Bs,Hs)]
    def bc(poly,al,ah,kl,kh,na=None,nr=None):
     na=max(i for i,j in poly)if na is None else na;nr=max(j for i,j in poly)if nr is None else nr
     pol={}
     for (a,r),v in poly.items():
      for i in range(a+1):
       for j in range(r+1):pol[i,j]=pol.get((i,j),F(0))+v*comb(a,i)*al**(a-i)*(ah-al)**i*comb(r,j)*kl**(r-j)*(kh-kl)**j
     return [sum(v*F(comb(i,a),comb(na,a))*F(comb(j,r),comb(nr,r))for(a,r),v in pol.items()if a<=i and r<=j)for i in range(na+1)for j in range(nr+1)]
    def IU(x):return (x**3+11*x*x+26*x+6)/(x*(x**3+12*x*x+36*x+24))
    def IL(x):return (x*x+8*x+11)/(x**3+9*x*x+18*x+6)
    def loghi(v):return F(logi(v.numerator,v.denominator)[1],S)
    def loglo(v):return F(logi(v.numerator,v.denominator)[0],S)
    def exphi(v):return F(expi(ceilF(v*S)),S)
    def entropy(k,a,J,q,c):
     cv=F(0)if q<=2 else CV[q]
     A=exphi(q/2+a/(2*k**3)*(-loglo(1-q*k*k)-q*k*k)+cv/(2*k*k))
     assert q*c/2>2
     ss=None if q<=1 else W/(k*(q-1))
     if ss is not None:assert ss>=c and q*ss/2>2
     def E(L):
      v=2*A/q*exphi(-2-(q*c/2-2)*L)*(1+IU(q*c*L/2))
      if ss is not None:v+=A*exphi(-2-(q*ss/2-2)*L)*((2-2/q)*(1+loghi(ss/c))+2*IU(ss*L/2)-2/q*IL(q*ss*L/2))
      return F(ceilF(v*10**10),10**10)
     LL=[F(i,40)for i in range(40,161)];EE=[E(L)for L in LL];marg=F(10)
     for l,h,u,v in zip(LL,LL[1:],EE,EE[1:]):
      slope=(v-u)/(h-l);rr=W-2-slope
      assert rr>0
      xx=min(h,max(l,1/rr));marg=min(marg,2+rr*xx-loghi(c*xx)-J/2-u+slope*l)
     assert 1/(W-2)<4
     marg=min(marg,2+4*(W-2)-loghi(4*c)-J/2-EE[-1])
     return marg


    # Sharper norm bound for kappa>=37/40.
    M=F(21,50);rr=F(381,1000)
    assert rr*rr>1-F(37,40)**2
    assert 1-6*rr*rr>0
    assert rr+rr*rr-2*rr**3<M
    assert 3*(1-F(37,40))<M
    xx=2*M+F(563,100)*M*M
    assert sum((xx**j/F(factorial(j))for j in range(25)),F(0))>1/(1-2*M)
    assert entropy(F(2,5),F(2,5),F(257,120),F(11,4),F(193,100))>F(1,100000)
    raw=[
     ('2/5', '33/80', '8/125', '3/40', '385091/200000', '4', '7/2', '141/100'),
     ('2/5', '33/80', '3/40', '1/10', '487063/250000', '4', '7/2', '31/20'),
     ('2/5', '33/80', '1/10', '1/8', '393921/200000', '4', '7/2', '7/4'),
     ('2/5', '33/80', '1/8', '3/20', '1989529/1000000', '4', '3', '83/50'),
     ('2/5', '33/80', '3/20', '7/40', '2008039/1000000', '4', '3', '83/50'),
     ('2/5', '33/80', '7/40', '1/5', '2025151/1000000', '4', '3', '42/25'),
     ('2/5', '33/80', '1/5', '9/40', '2040881/1000000', '4', '3', '17/10'),
     ('2/5', '33/80', '9/40', '1/4', '1027623/500000', '4', '3', '87/50'),
     ('2/5', '33/80', '1/4', '11/40', '2059667/1000000', '3', '3', '93/50'),
     ('2/5', '33/80', '11/40', '3/10', '2069363/1000000', '3', '3', '2'),
     ('2/5', '33/80', '3/10', '13/40', '2071717/1000000', '3', '11/4', '47/25'),
     ('2/5', '33/80', '13/40', '7/20', '25877/12500', '5', '11/4', '19/10'),
     ('2/5', '33/80', '7/20', '3/8', '1027047/500000', '5', '11/4', '19/10'),
     ('2/5', '33/80', '3/8', '2/5', '2021743/1000000', '5', '11/4', '48/25'),
     ('2/5', '33/80', '2/5', '33/80', '1969657/1000000', '5', '11/4', '19/10'),
     ('33/80', '17/40', '35937/512000', '3/40', '472973/250000', '4', '7/2', '151/100'),
     ('33/80', '17/40', '3/40', '1/10', '479177/250000', '4', '7/2', '7/4'),
     ('33/80', '17/40', '1/10', '1/8', '1940019/1000000', '4', '3', '41/25'),
     ('33/80', '17/40', '1/8', '3/20', '24523/12500', '4', '3', '83/50'),
     ('33/80', '17/40', '3/20', '7/40', '1982191/1000000', '4', '3', '42/25'),
     ('33/80', '17/40', '7/40', '1/5', '200109/100000', '4', '3', '42/25'),
     ('33/80', '17/40', '1/5', '9/40', '2018559/1000000', '4', '3', '89/50'),
     ('33/80', '17/40', '9/40', '1/4', '2034619/1000000', '4', '3', '97/50'),
     ('33/80', '17/40', '1/4', '11/40', '204089/100000', '3', '11/4', '93/50'),
     ('33/80', '17/40', '11/40', '3/10', '102657/50000', '3', '11/4', '47/25'),
     ('33/80', '17/40', '3/10', '13/40', '2057571/1000000', '3', '11/4', '19/10'),
     ('33/80', '17/40', '13/40', '7/20', '102883/50000', '3', '11/4', '2'),
     ('33/80', '17/40', '7/20', '3/8', '2046949/1000000', '5', '11/4', '52/25'),
     ('33/80', '17/40', '3/8', '2/5', '504437/250000', '5', '11/4', '53/25'),
     ('33/80', '17/40', '2/5', '17/40', '1968853/1000000', '5', '11/4', '53/25'),
     ('17/40', '7/16', '4913/64000', '1/10', '1881667/1000000', '4', '3', '81/50'),
     ('17/40', '7/16', '1/10', '1/8', '953487/500000', '4', '3', '41/25'),
     ('17/40', '7/16', '1/8', '3/20', '482683/250000', '4', '3', '83/50'),
     ('17/40', '7/16', '3/20', '7/40', '976481/500000', '4', '3', '42/25'),
     ('17/40', '7/16', '7/40', '1/5', '246711/125000', '4', '3', '91/50'),
     ('17/40', '7/16', '1/5', '9/40', '398587/200000', '4', '3', '2'),
     ('17/40', '7/16', '9/40', '1/4', '2010731/1000000', '4', '11/4', '93/50'),
     ('17/40', '7/16', '1/4', '11/40', '403781/200000', '3', '11/4', '47/25'),
     ('17/40', '7/16', '11/40', '3/10', '2033839/1000000', '3', '11/4', '49/25'),
     ('17/40', '7/16', '3/10', '13/40', '2040837/1000000', '3', '11/4', '21/10'),
     ('17/40', '7/16', '13/40', '7/20', '204159/100000', '3', '11/4', '56/25'),
     ('17/40', '7/16', '7/20', '3/8', '101871/50000', '5', '5/2', '209/100'),
     ('17/40', '7/16', '3/8', '2/5', '1005813/500000', '5', '5/2', '209/100'),
     ('17/40', '7/16', '2/5', '17/40', '245777/125000', '5', '5/2', '209/100'),
     ('17/40', '7/16', '17/40', '7/16', '948759/500000', '5', '5/2', '209/100'),
     ('7/16', '9/20', '343/4096', '1/10', '921509/500000', '4', '3', '81/50'),
     ('7/16', '9/20', '1/10', '1/8', '467587/250000', '4', '3', '41/25'),
     ('7/16', '9/20', '1/8', '3/20', '1896067/1000000', '4', '3', '83/50'),
     ('7/16', '9/20', '3/20', '7/40', '1920199/1000000', '4', '3', '91/50'),
     ('7/16', '9/20', '7/40', '1/5', '1942773/1000000', '4', '11/4', '91/50'),
     ('7/16', '9/20', '1/5', '9/40', '98191/50000', '4', '11/4', '46/25'),
     ('7/16', '9/20', '9/40', '1/4', '495843/250000', '4', '11/4', '93/50'),
     ('7/16', '9/20', '1/4', '11/40', '498371/250000', '3', '11/4', '101/50'),
     ('7/16', '9/20', '11/40', '3/10', '2011211/1000000', '3', '11/4', '11/5'),
     ('7/16', '9/20', '3/10', '13/40', '1010443/500000', '3', '5/2', '207/100'),
     ('7/16', '9/20', '13/40', '7/20', '2023061/1000000', '3', '5/2', '209/100'),
     ('7/16', '9/20', '7/20', '3/8', '1011277/500000', '3', '5/2', '211/100'),
     ('7/16', '9/20', '3/8', '2/5', '125193/62500', '5', '5/2', '211/100'),
     ('7/16', '9/20', '2/5', '17/40', '980719/500000', '5', '5/2', '211/100'),
     ('7/16', '9/20', '17/40', '9/20', '1896561/1000000', '5', '5/2', '211/100'),
     ('9/20', '37/80', '729/8000', '1/10', '1800693/1000000', '4', '3', '81/50'),
     ('9/20', '37/80', '1/10', '1/8', '1830059/1000000', '4', '3', '41/25'),
     ('9/20', '37/80', '1/8', '3/20', '928873/500000', '4', '3', '89/50'),
     ('9/20', '37/80', '3/20', '7/40', '1883787/1000000', '4', '11/4', '91/50'),
     ('9/20', '37/80', '7/40', '1/5', '1908213/1000000', '4', '11/4', '46/25'),
     ('9/20', '37/80', '1/5', '9/40', '965531/500000', '4', '11/4', '93/50'),
     ('9/20', '37/80', '9/40', '1/4', '1952373/1000000', '4', '11/4', '103/50'),
     ('9/20', '37/80', '1/4', '11/40', '1964433/1000000', '3', '5/2', '41/20'),
     ('9/20', '37/80', '11/40', '3/10', '992521/500000', '3', '5/2', '207/100'),
     ('9/20', '37/80', '3/10', '13/40', '1997481/1000000', '3', '5/2', '209/100'),
     ('9/20', '37/80', '13/40', '7/20', '500451/250000', '3', '5/2', '211/100'),
     ('9/20', '37/80', '7/20', '3/8', '500463/250000', '3', '5/2', '9/4'),
     ('9/20', '37/80', '3/8', '2/5', '199187/100000', '5', '5/2', '47/20'),
     ('9/20', '37/80', '2/5', '17/40', '390847/200000', '5', '5/2', '237/100'),
     ('9/20', '37/80', '17/40', '9/20', '1893471/1000000', '5', '5/2', '233/100'),
     ('9/20', '37/80', '9/20', '37/80', '1939267/1000000', '3', '12/5', '9/4'),
     ('37/80', '19/40', '50653/512000', '1/10', '877333/500000', '4', '3', '81/50'),
     ('37/80', '19/40', '1/10', '1/8', '893033/500000', '4', '3', '43/25'),
     ('37/80', '19/40', '1/8', '3/20', '907859/500000', '4', '11/4', '9/5'),
     ('37/80', '19/40', '3/20', '7/40', '921829/500000', '4', '11/4', '91/50'),
     ('37/80', '19/40', '7/40', '1/5', '467481/250000', '4', '11/4', '46/25'),
     ('37/80', '19/40', '1/5', '9/40', '1894559/1000000', '4', '11/4', '103/50'),
     ('37/80', '19/40', '9/40', '1/4', '1917607/1000000', '4', '5/2', '203/100'),
     ('37/80', '19/40', '1/4', '11/40', '965803/500000', '3', '5/2', '41/20'),
     ('37/80', '19/40', '11/40', '3/10', '391033/200000', '3', '5/2', '207/100'),
     ('37/80', '19/40', '3/10', '13/40', '1970431/1000000', '3', '5/2', '219/100'),
     ('37/80', '19/40', '13/40', '7/20', '1977469/1000000', '3', '12/5', '219/100'),
     ('37/80', '19/40', '7/20', '3/8', '1978183/1000000', '3', '12/5', '221/100'),
     ('37/80', '19/40', '3/8', '2/5', '1976353/1000000', '3', '12/5', '233/100'),
     ('37/80', '19/40', '2/5', '17/40', '1944361/1000000', '5', '12/5', '237/100'),
     ('37/80', '19/40', '17/40', '9/20', '75519/40000', '5', '12/5', '47/20'),
     ('37/80', '19/40', '9/20', '19/40', '1924941/1000000', '3', '23/10', '117/50'),
     ('19/40', '39/80', '6859/64000', '1/8', '217297/125000', '4', '3', '19/10'),
     ('19/40', '39/80', '1/8', '3/20', '70799/40000', '4', '11/4', '9/5'),
     ('19/40', '39/80', '3/20', '7/40', '112487/62500', '4', '11/4', '91/50'),
     ('19/40', '39/80', '7/40', '1/5', '1827869/1000000', '4', '11/4', '101/50'),
     ('19/40', '39/80', '1/5', '9/40', '115891/62500', '4', '5/2', '201/100'),
     ('19/40', '39/80', '9/40', '1/4', '469751/250000', '4', '5/2', '203/100'),
     ('19/40', '39/80', '1/4', '11/40', '1894909/1000000', '3', '5/2', '207/100'),
     ('19/40', '39/80', '11/40', '3/10', '960733/500000', '3', '5/2', '221/100'),
     ('19/40', '39/80', '3/10', '13/40', '4849/2500', '3', '12/5', '217/100'),
     ('19/40', '39/80', '13/40', '7/20', '487347/250000', '3', '12/5', '229/100'),
     ('19/40', '39/80', '7/20', '3/8', '975749/500000', '3', '12/5', '243/100'),
     ('19/40', '39/80', '3/8', '2/5', '390183/200000', '3', '23/10', '23/10'),
     ('19/40', '39/80', '2/5', '17/40', '1931621/1000000', '5', '23/10', '117/50'),
     ('19/40', '39/80', '17/40', '9/20', '1879849/1000000', '5', '23/10', '58/25'),
     ('19/40', '77/160', '9/20', '37/80', '1906957/1000000', '3', '23/10', '117/50'),
     ('19/40', '77/160', '37/80', '19/40', '189271/100000', '3', '23/10', '59/25'),
     ('77/160', '39/80', '9/20', '37/80', '474129/250000', '3', '23/10', '123/50'),
     ('77/160', '39/80', '37/80', '19/40', '376573/200000', '3', '23/10', '62/25'),
     ('19/40', '39/80', '19/40', '39/80', '1876533/1000000', '3', '23/10', '5/2'),
     ('39/80', '1/2', '59319/512000', '1/8', '337409/200000', '4', '11/4', '89/50'),
     ('39/80', '1/2', '1/8', '3/20', '860281/500000', '4', '11/4', '9/5'),
     ('39/80', '1/2', '3/20', '7/40', '87611/50000', '4', '11/4', '49/25'),
     ('39/80', '1/2', '7/40', '1/5', '1782067/1000000', '4', '5/2', '201/100'),
     ('39/80', '1/2', '1/5', '9/40', '1810157/1000000', '4', '5/2', '203/100'),
     ('39/80', '1/2', '9/40', '1/4', '459137/250000', '4', '5/2', '41/20'),
     ('39/80', '1/2', '1/4', '11/40', '185431/100000', '3', '5/2', '217/100'),
     ('39/80', '1/2', '11/40', '3/10', '1883893/1000000', '3', '12/5', '217/100'),
     ('39/80', '1/2', '3/10', '13/40', '952457/500000', '3', '12/5', '231/100'),
     ('39/80', '1/2', '13/40', '7/20', '95873/50000', '3', '23/10', '57/25'),
     ('39/80', '1/2', '7/20', '3/8', '60051/31250', '3', '23/10', '117/50'),
     ('39/80', '79/160', '3/8', '31/80', '1921633/1000000', '3', '23/10', '23/10'),
     ('39/80', '79/160', '31/80', '2/5', '1920611/1000000', '3', '23/10', '59/25'),
     ('79/160', '1/2', '3/8', '31/80', '1905677/1000000', '3', '23/10', '12/5'),
     ('79/160', '1/2', '31/80', '2/5', '238143/125000', '3', '23/10', '123/50'),
     ('39/80', '79/160', '2/5', '33/80', '1915887/1000000', '5', '23/10', '12/5'),
     ('39/80', '79/160', '33/80', '17/40', '947747/500000', '5', '23/10', '12/5'),
     ('79/160', '1/2', '2/5', '33/80', '380539/200000', '3', '9/4', '119/50'),
     ('79/160', '1/2', '33/80', '17/40', '943857/500000', '5', '9/4', '119/50'),
     ('39/80', '1/2', '17/40', '9/20', '1868939/1000000', '5', '9/4', '61/25'),
     ('39/80', '79/160', '9/20', '37/80', '1885079/1000000', '3', '9/4', '12/5'),
     ('39/80', '79/160', '37/80', '19/40', '117001/62500', '3', '9/4', '61/25'),
     ('79/160', '159/320', '9/20', '73/160', '1872627/1000000', '3', '9/4', '61/25'),
     ('79/160', '159/320', '73/160', '37/80', '186663/100000', '3', '9/4', '61/25'),
     ('159/320', '1/2', '9/20', '73/160', '933009/500000', '3', '9/4', '62/25'),
     ('159/320', '1/2', '73/160', '37/80', '465041/250000', '3', '9/4', '5/2'),
     ('79/160', '159/320', '37/80', '15/32', '372029/200000', '3', '9/4', '123/50'),
     ('79/160', '159/320', '15/32', '19/40', '926587/500000', '3', '9/4', '62/25'),
     ('159/320', '1/2', '37/80', '15/32', '1853821/1000000', '3', '9/4', '63/25'),
     ('159/320', '1/2', '15/32', '19/40', '115437/62500', '3', '9/4', '63/25'),
     ('39/80', '79/160', '19/40', '39/80', '928509/500000', '3', '9/4', '123/50'),
     ('39/80', '79/160', '39/80', '79/160', '460027/250000', '3', '9/4', '123/50'),
     ('79/160', '1/2', '19/40', '39/80', '922861/500000', '3', '9/4', '129/50'),
     ('79/160', '1/2', '39/80', '1/2', '914693/500000', '3', '11/5', '123/50'),
     ('1/2', '41/80', '1/8', '3/20', '166757/100000', '4', '11/4', '47/25'),
     ('1/2', '41/80', '3/20', '7/40', '850513/500000', '4', '5/2', '199/100'),
     ('1/2', '41/80', '7/40', '1/5', '1732589/1000000', '4', '5/2', '201/100'),
     ('1/2', '41/80', '1/5', '9/40', '1762321/1000000', '4', '5/2', '203/100'),
     ('1/2', '41/80', '9/40', '1/4', '895143/500000', '4', '5/2', '43/20'),
     ('1/2', '41/80', '1/4', '11/40', '1809837/1000000', '3', '12/5', '43/20'),
     ('1/2', '41/80', '11/40', '3/10', '184121/100000', '4', '12/5', '229/100'),
     ('1/2', '41/80', '3/10', '13/40', '1864337/1000000', '4', '23/10', '57/25'),
     ('1/2', '41/80', '13/40', '7/20', '940831/500000', '3', '23/10', '119/50'),
     ('1/2', '41/80', '7/20', '3/8', '472113/250000', '3', '9/4', '119/50'),
     ('1/2', '81/160', '3/8', '31/80', '1888893/1000000', '3', '9/4', '59/25'),
     ('1/2', '81/160', '31/80', '2/5', '1888697/1000000', '3', '9/4', '12/5'),
     ('81/160', '41/80', '3/8', '31/80', '935653/500000', '3', '9/4', '121/50'),
     ('81/160', '41/80', '31/80', '2/5', '467819/250000', '3', '9/4', '5/2'),
     ('1/2', '81/160', '2/5', '33/80', '377373/200000', '3', '9/4', '123/50'),
     ('1/2', '161/320', '33/80', '67/160', '469799/250000', '5', '9/4', '12/5'),
     ('1/2', '161/320', '67/160', '17/40', '1867979/1000000', '5', '9/4', '12/5'),
     ('161/320', '81/160', '33/80', '67/160', '1874661/1000000', '5', '9/4', '123/50'),
     ('161/320', '81/160', '67/160', '17/40', '372753/200000', '5', '9/4', '123/50'),
     ('81/160', '163/320', '2/5', '13/32', '467513/250000', '3', '9/4', '123/50'),
     ('81/160', '163/320', '13/32', '33/80', '1868661/1000000', '3', '9/4', '62/25'),
     ('163/320', '41/80', '2/5', '13/32', '1861279/1000000', '3', '9/4', '63/25'),
     ('163/320', '41/80', '13/32', '33/80', '465009/250000', '3', '9/4', '127/50'),
     ('81/160', '163/320', '33/80', '67/160', '373351/200000', '3', '9/4', '63/25'),
     ('81/160', '163/320', '67/160', '17/40', '1859371/1000000', '5', '9/4', '127/50'),
     ('163/320', '41/80', '33/80', '67/160', '74331/40000', '3', '11/5', '61/25'),
     ('163/320', '41/80', '67/160', '17/40', '4637/2500', '5', '11/5', '61/25'),
     ('1/2', '81/160', '17/40', '7/16', '1855169/1000000', '5', '9/4', '63/25'),
     ('1/2', '81/160', '7/16', '9/20', '182451/100000', '5', '9/4', '62/25'),
     ('81/160', '41/80', '17/40', '7/16', '461803/250000', '5', '11/5', '123/50'),
     ('81/160', '41/80', '7/16', '9/20', '1817873/1000000', '5', '11/5', '61/25'),
     ('1/2', '161/320', '9/20', '73/160', '116197/62500', '3', '9/4', '127/50'),
     ('1/2', '161/320', '73/160', '37/80', '1853439/1000000', '3', '9/4', '64/25'),
     ('161/320', '323/640', '9/20', '29/64', '463007/250000', '3', '9/4', '127/50'),
     ('161/320', '323/640', '29/64', '73/160', '1849303/1000000', '3', '9/4', '64/25'),
     ('323/640', '81/160', '9/20', '29/64', '184837/100000', '3', '9/4', '129/50'),
     ('323/640', '81/160', '29/64', '73/160', '1845679/1000000', '3', '11/5', '61/25'),
     ('161/320', '81/160', '73/160', '37/80', '369291/200000', '3', '11/5', '61/25'),
     ('1/2', '161/320', '37/80', '15/32', '1847237/1000000', '3', '9/4', '129/50'),
     ('1/2', '161/320', '15/32', '19/40', '460137/250000', '3', '9/4', '129/50'),
     ('161/320', '81/160', '37/80', '15/32', '230049/125000', '3', '11/5', '123/50'),
     ('161/320', '81/160', '15/32', '19/40', '1833841/1000000', '3', '11/5', '62/25'),
     ('81/160', '163/320', '9/20', '73/160', '1844647/1000000', '3', '11/5', '62/25'),
     ('81/160', '163/320', '73/160', '37/80', '459803/250000', '3', '11/5', '5/2'),
     ('163/320', '327/640', '9/20', '29/64', '183701/100000', '3', '11/5', '62/25'),
     ('163/320', '327/640', '29/64', '73/160', '917211/500000', '3', '11/5', '5/2'),
     ('327/640', '41/80', '9/20', '29/64', '366619/200000', '3', '11/5', '63/25'),
     ('327/640', '41/80', '29/64', '73/160', '1830541/1000000', '3', '11/5', '63/25'),
     ('163/320', '327/640', '73/160', '147/320', '183171/100000', '3', '11/5', '5/2'),
     ('163/320', '327/640', '147/320', '37/80', '457219/250000', '3', '11/5', '63/25'),
     ('327/640', '41/80', '73/160', '147/320', '1827863/1000000', '3', '11/5', '63/25'),
     ('327/640', '41/80', '147/320', '37/80', '912531/500000', '3', '11/5', '127/50'),
     ('81/160', '163/320', '37/80', '15/32', '916643/500000', '3', '11/5', '63/25'),
     ('81/160', '163/320', '15/32', '19/40', '228359/125000', '3', '11/5', '127/50'),
     ('163/320', '41/80', '37/80', '15/32', '1825919/1000000', '3', '11/5', '129/50'),
     ('163/320', '41/80', '15/32', '19/40', '1819639/1000000', '3', '11/5', '129/50'),
     ('1/2', '81/160', '19/40', '39/80', '1833377/1000000', '3', '11/5', '127/50'),
     ('1/2', '81/160', '39/80', '1/2', '1817601/1000000', '3', '11/5', '127/50'),
     ('81/160', '163/320', '19/40', '77/160', '1819973/1000000', '3', '11/5', '127/50'),
     ('81/160', '163/320', '77/160', '39/80', '362519/200000', '3', '11/5', '64/25'),
     ('163/320', '41/80', '19/40', '77/160', '1812873/1000000', '3', '11/5', '13/5'),
     ('163/320', '41/80', '77/160', '39/80', '1805627/1000000', '3', '11/5', '131/50'),
     ('81/160', '163/320', '39/80', '79/160', '90237/50000', '3', '11/5', '64/25'),
     ('81/160', '163/320', '79/160', '1/2', '1796413/1000000', '3', '11/5', '129/50'),
     ('163/320', '41/80', '39/80', '79/160', '112369/62500', '3', '11/5', '131/50'),
     ('163/320', '41/80', '79/160', '1/2', '1789709/1000000', '3', '11/5', '131/50'),
     ('1/2', '81/160', '1/2', '81/160', '899969/500000', '3', '11/5', '127/50'),
     ('81/160', '41/80', '1/2', '81/160', '1787619/1000000', '3', '11/5', '133/50'),
     ('81/160', '41/80', '81/160', '41/80', '1778361/1000000', '3', '11/5', '133/50'),
     ('41/80', '21/40', '68921/512000', '3/20', '1611137/1000000', '4', '11/4', '51/25'),
     ('41/80', '21/40', '3/20', '7/40', '1646339/1000000', '4', '5/2', '199/100'),
     ('41/80', '21/40', '7/40', '1/5', '41989/25000', '4', '5/2', '201/100'),
     ('41/80', '21/40', '1/5', '9/40', '106929/62500', '4', '5/2', '207/100'),
     ('41/80', '21/40', '9/40', '1/4', '870161/500000', '4', '12/5', '213/100'),
     ('41/80', '21/40', '1/4', '11/40', '1761583/1000000', '3', '12/5', '221/100'),
     ('41/80', '21/40', '11/40', '3/10', '1794021/1000000', '4', '23/10', '113/50'),
     ('41/80', '21/40', '3/10', '13/40', '113653/62500', '4', '23/10', '59/25'),
     ('41/80', '21/40', '13/40', '7/20', '920701/500000', '4', '9/4', '12/5'),
     ('41/80', '21/40', '7/20', '3/8', '1851407/1000000', '3', '11/5', '121/50'),
     ('41/80', '83/160', '3/8', '31/80', '185289/100000', '3', '9/4', '127/50'),
     ('41/80', '83/160', '31/80', '2/5', '1852961/1000000', '3', '11/5', '61/25'),
     ('83/160', '21/40', '3/8', '31/80', '916777/500000', '3', '11/5', '61/25'),
     ('83/160', '21/40', '31/80', '2/5', '458463/250000', '3', '11/5', '63/25'),
     ('41/80', '33/64', '2/5', '13/32', '231533/125000', '3', '11/5', '121/50'),
     ('41/80', '33/64', '13/32', '33/80', '1851167/1000000', '3', '11/5', '61/25'),
     ('33/64', '83/160', '2/5', '13/32', '1843009/1000000', '3', '11/5', '61/25'),
     ('33/64', '83/160', '13/32', '33/80', '230257/125000', '3', '11/5', '123/50'),
     ('41/80', '33/64', '33/80', '67/160', '1849551/1000000', '3', '11/5', '61/25'),
     ('41/80', '33/64', '67/160', '17/40', '923709/500000', '3', '11/5', '62/25'),
     ('33/64', '83/160', '33/80', '67/160', '1840583/1000000', '3', '11/5', '5/2'),
     ('33/64', '83/160', '67/160', '17/40', '1838591/1000000', '3', '11/5', '63/25'),
     ('83/160', '167/320', '2/5', '13/32', '458379/250000', '3', '11/5', '62/25'),
     ('83/160', '167/320', '13/32', '33/80', '1832707/1000000', '3', '11/5', '63/25'),
     ('167/320', '21/40', '2/5', '13/32', '1823789/1000000', '3', '11/5', '127/50'),
     ('167/320', '21/40', '13/32', '33/80', '1823121/1000000', '3', '11/5', '64/25'),
     ('83/160', '167/320', '33/80', '67/160', '915687/500000', '3', '11/5', '127/50'),
     ('83/160', '333/640', '67/160', '27/64', '914761/500000', '3', '11/5', '63/25'),
     ('83/160', '333/640', '27/64', '17/40', '1828401/1000000', '3', '11/5', '127/50'),
     ('333/640', '167/320', '67/160', '27/64', '1824897/1000000', '3', '11/5', '127/50'),
     ('333/640', '167/320', '27/64', '17/40', '182381/100000', '3', '11/5', '64/25'),
     ('167/320', '67/128', '33/80', '133/320', '1821927/1000000', '3', '11/5', '127/50'),
     ('167/320', '67/128', '133/320', '67/160', '364227/200000', '3', '11/5', '64/25'),
     ('67/128', '21/40', '33/80', '133/320', '454279/250000', '3', '11/5', '64/25'),
     ('67/128', '21/40', '133/320', '67/160', '1816357/1000000', '3', '11/5', '129/50'),
     ('167/320', '67/128', '67/160', '27/64', '455053/250000', '3', '11/5', '129/50'),
     ('167/320', '67/128', '27/64', '17/40', '45479/25000', '3', '11/5', '129/50'),
     ('67/128', '21/40', '67/160', '27/64', '453867/250000', '3', '11/5', '13/5'),
     ('67/128', '21/40', '27/64', '17/40', '1814449/1000000', '3', '11/5', '131/50'),
     ('41/80', '33/64', '17/40', '69/160', '919277/500000', '5', '11/5', '62/25'),
     ('41/80', '33/64', '69/160', '7/16', '1825411/1000000', '5', '11/5', '62/25'),
     ('33/64', '83/160', '17/40', '69/160', '1833967/1000000', '5', '11/5', '127/50'),
     ('33/64', '83/160', '69/160', '7/16', '1821161/1000000', '5', '11/5', '127/50'),
     ('41/80', '83/160', '7/16', '9/20', '362111/200000', '5', '11/5', '64/25'),
     ('83/160', '333/640', '17/40', '137/320', '114197/62500', '3', '11/5', '127/50'),
     ('83/160', '333/640', '137/320', '69/160', '455797/250000', '5', '11/5', '64/25'),
     ('333/640', '167/320', '17/40', '137/320', '364519/200000', '3', '11/5', '129/50'),
     ('333/640', '167/320', '137/320', '69/160', '1820833/1000000', '5', '11/5', '129/50'),
     ('83/160', '333/640', '69/160', '139/320', '908373/500000', '5', '11/5', '64/25'),
     ('83/160', '333/640', '139/320', '7/16', '1809877/1000000', '5', '11/5', '64/25'),
     ('333/640', '167/320', '69/160', '139/320', '453619/250000', '5', '11/5', '129/50'),
     ('333/640', '167/320', '139/320', '7/16', '903847/500000', '5', '11/5', '129/50'),
     ('167/320', '67/128', '17/40', '137/320', '908989/500000', '3', '11/5', '13/5'),
     ('167/320', '669/1280', '137/320', '55/128', '1816667/1000000', '3', '11/5', '129/50'),
     ('167/320', '669/1280', '55/128', '69/160', '363071/200000', '5', '11/5', '13/5'),
     ('669/1280', '67/128', '137/320', '55/128', '113397/62500', '3', '11/5', '13/5'),
     ('669/1280', '67/128', '55/128', '69/160', '1813657/1000000', '3', '11/5', '13/5'),
     ('67/128', '671/1280', '17/40', '273/640', '1813301/1000000', '3', '11/5', '13/5'),
     ('67/128', '671/1280', '273/640', '137/320', '906339/500000', '3', '11/5', '13/5'),
     ('671/1280', '21/40', '17/40', '273/640', '90547/50000', '3', '11/5', '131/50'),
     ('671/1280', '21/40', '273/640', '137/320', '72413/40000', '3', '11/5', '131/50'),
     ('67/128', '671/1280', '137/320', '55/128', '1812023/1000000', '3', '11/5', '131/50'),
     ('67/128', '671/1280', '55/128', '69/160', '226417/125000', '3', '11/5', '131/50'),
     ('671/1280', '21/40', '137/320', '55/128', '1809679/1000000', '3', '11/5', '131/50'),
     ('671/1280', '21/40', '55/128', '69/160', '1809/1000', '3', '11/5', '66/25'),
     ('167/320', '67/128', '69/160', '139/320', '1812167/1000000', '5', '11/5', '131/50'),
     ('167/320', '67/128', '139/320', '7/16', '180547/100000', '5', '11/5', '131/50'),
     ('67/128', '671/1280', '69/160', '277/640', '1809817/1000000', '5', '11/5', '131/50'),
     ('67/128', '671/1280', '277/640', '139/320', '903283/500000', '5', '11/5', '131/50'),
     ('671/1280', '1343/2560', '69/160', '553/1280', '56509/31250', '3', '11/5', '131/50'),
     ('671/1280', '1343/2560', '553/1280', '277/640', '903513/500000', '5', '11/5', '131/50'),
     ('1343/2560', '21/40', '69/160', '553/1280', '1807119/1000000', '3', '11/5', '66/25'),
     ('1343/2560', '21/40', '553/1280', '277/640', '1806433/1000000', '5', '11/5', '66/25'),
     ('671/1280', '21/40', '277/640', '139/320', '902699/500000', '5', '11/5', '66/25'),
     ('67/128', '21/40', '139/320', '7/16', '1803207/1000000', '5', '43/20', '249/100'),
     ('83/160', '167/320', '7/16', '71/160', '1802573/1000000', '5', '11/5', '13/5'),
     ('83/160', '167/320', '71/160', '9/20', '14293/8000', '5', '11/5', '13/5'),
     ('167/320', '21/40', '7/16', '71/160', '1798339/1000000', '5', '43/20', '251/100'),
     ('167/320', '21/40', '71/160', '9/20', '1782739/1000000', '5', '43/20', '251/100'),
     ('41/80', '33/64', '9/20', '73/160', '1775433/1000000', '5', '11/5', '61/25'),
     ('41/80', '33/64', '73/160', '37/80', '219379/125000', '5', '11/5', '61/25'),
     ('33/64', '83/160', '9/20', '73/160', '1772213/1000000', '5', '11/5', '5/2'),
     ('33/64', '83/160', '73/160', '37/80', '1752159/1000000', '5', '11/5', '62/25'),
     ('41/80', '33/64', '37/80', '15/32', '433161/250000', '5', '9/4', '64/25'),
     ('41/80', '33/64', '15/32', '19/40', '8541/5000', '5', '9/4', '127/50'),
     ('33/64', '83/160', '37/80', '15/32', '43253/25000', '5', '11/5', '123/50'),
     ('33/64', '83/160', '15/32', '19/40', '426507/250000', '5', '11/5', '61/25'),
     ('83/160', '167/320', '9/20', '73/160', '884417/500000', '5', '11/5', '129/50'),
     ('83/160', '167/320', '73/160', '37/80', '174913/100000', '5', '11/5', '64/25'),
     ('167/320', '21/40', '9/20', '73/160', '1765299/1000000', '5', '11/5', '66/25'),
     ('167/320', '21/40', '73/160', '37/80', '436487/250000', '5', '11/5', '131/50'),
     ('83/160', '167/320', '37/80', '15/32', '431861/250000', '5', '11/5', '63/25'),
     ('83/160', '167/320', '15/32', '19/40', '851853/500000', '5', '11/5', '5/2'),
     ('167/320', '21/40', '37/80', '15/32', '862309/500000', '5', '11/5', '13/5'),
     ('167/320', '21/40', '15/32', '19/40', '1701237/1000000', '5', '11/5', '64/25'),
     ('41/80', '83/160', '19/40', '39/80', '168163/100000', '5', '11/5', '61/25'),
     ('41/80', '83/160', '39/80', '1/2', '1621827/1000000', '5', '9/4', '63/25'),
     ('83/160', '167/320', '19/40', '77/160', '335569/200000', '5', '11/5', '123/50'),
     ('83/160', '167/320', '77/160', '39/80', '1783123/1000000', '3', '43/20', '259/100'),
     ('167/320', '21/40', '19/40', '77/160', '837867/500000', '5', '11/5', '127/50'),
     ('167/320', '21/40', '77/160', '39/80', '1648037/1000000', '5', '11/5', '5/2'),
     ('83/160', '21/40', '39/80', '1/2', '809733/500000', '5', '11/5', '5/2'),
     ('41/80', '83/160', '1/2', '41/80', '1774197/1000000', '3', '43/20', '261/100'),
     ('41/80', '83/160', '41/80', '83/160', '877871/500000', '3', '43/20', '259/100'),
     ('83/160', '167/320', '1/2', '81/160', '1551729/1000000', '5', '9/4', '123/50'),
     ('83/160', '167/320', '81/160', '41/80', '875461/500000', '3', '43/20', '263/100'),
     ('167/320', '21/40', '1/2', '81/160', '775531/500000', '5', '9/4', '63/25'),
     ('167/320', '21/40', '81/160', '41/80', '217921/125000', '3', '17/8', '259/100'),
     ('83/160', '21/40', '41/80', '21/40', '108857/62500', '3', '17/8', '53/20'),
     ('21/40', '43/80', '9261/64000', '3/20', '1551439/1000000', '4', '5/2', '197/100'),
     ('21/40', '43/80', '3/20', '7/40', '99271/62500', '4', '5/2', '199/100'),
     ('21/40', '43/80', '7/40', '1/5', '1623151/1000000', '4', '5/2', '201/100'),
     ('21/40', '43/80', '1/5', '9/40', '103497/62500', '4', '5/2', '9/4'),
     ('21/40', '43/80', '9/40', '1/4', '52713/31250', '4', '12/5', '217/100'),
     ('21/40', '43/80', '1/4', '11/40', '854851/500000', '3', '23/10', '56/25'),
     ('21/40', '43/80', '11/40', '3/10', '43577/25000', '4', '23/10', '57/25'),
     ('21/40', '43/80', '3/10', '13/40', '1768679/1000000', '4', '9/4', '117/50'),
     ('21/40', '43/80', '13/40', '7/20', '1792743/1000000', '4', '11/5', '12/5'),
     ('21/40', '43/80', '7/20', '3/8', '181061/100000', '3', '11/5', '13/5'),
     ('21/40', '17/32', '3/8', '31/80', '1813291/1000000', '3', '11/5', '127/50'),
     ('21/40', '169/320', '31/80', '63/160', '1813827/1000000', '3', '11/5', '5/2'),
     ('21/40', '169/320', '63/160', '2/5', '453477/250000', '3', '11/5', '127/50'),
     ('169/320', '17/32', '31/80', '63/160', '901749/500000', '3', '11/5', '64/25'),
     ('169/320', '17/32', '63/160', '2/5', '360733/200000', '3', '11/5', '13/5'),
     ('17/32', '43/80', '3/8', '31/80', '1792127/1000000', '3', '43/20', '249/100'),
     ('17/32', '43/80', '31/80', '2/5', '448307/250000', '3', '43/20', '251/100'),
     ('21/40', '169/320', '2/5', '13/32', '1813829/1000000', '3', '11/5', '129/50'),
     ('21/40', '169/320', '13/32', '33/80', '1813301/1000000', '3', '11/5', '131/50'),
     ('169/320', '17/32', '2/5', '13/32', '1803641/1000000', '3', '43/20', '249/100'),
     ('169/320', '17/32', '13/32', '33/80', '1803251/1000000', '3', '43/20', '249/100'),
     ('21/40', '337/640', '33/80', '133/320', '362449/200000', '3', '11/5', '13/5'),
     ('21/40', '337/640', '133/320', '67/160', '1811521/1000000', '3', '11/5', '13/5'),
     ('337/640', '169/320', '33/80', '133/320', '1807317/1000000', '3', '11/5', '131/50'),
     ('337/640', '169/320', '133/320', '67/160', '903313/500000', '3', '43/20', '249/100'),
     ('21/40', '337/640', '67/160', '27/64', '362133/200000', '3', '11/5', '131/50'),
     ('21/40', '673/1280', '27/64', '271/640', '22621/12500', '3', '11/5', '13/5'),
     ('21/40', '673/1280', '271/640', '17/40', '904569/500000', '3', '11/5', '131/50'),
     ('673/1280', '337/640', '27/64', '271/640', '1807273/1000000', '3', '11/5', '131/50'),
     ('673/1280', '337/640', '271/640', '17/40', '90337/50000', '3', '11/5', '131/50'),
     ('337/640', '169/320', '67/160', '27/64', '451451/250000', '3', '43/20', '249/100'),
     ('337/640', '169/320', '27/64', '17/40', '451213/250000', '3', '43/20', '249/100'),
     ('169/320', '17/32', '33/80', '67/160', '1802331/1000000', '3', '43/20', '251/100'),
     ('169/320', '339/640', '67/160', '27/64', '360177/200000', '3', '43/20', '249/100'),
     ('169/320', '339/640', '27/64', '17/40', '359993/200000', '3', '43/20', '251/100'),
     ('339/640', '17/32', '67/160', '27/64', '448977/250000', '3', '43/20', '251/100'),
     ('339/640', '17/32', '27/64', '17/40', '1795021/1000000', '3', '43/20', '251/100'),
     ('17/32', '171/320', '2/5', '13/32', '179323/100000', '3', '43/20', '249/100'),
     ('17/32', '171/320', '13/32', '33/80', '896487/500000', '3', '43/20', '251/100'),
     ('171/320', '43/80', '2/5', '13/32', '891313/500000', '3', '43/20', '253/100'),
     ('171/320', '43/80', '13/32', '33/80', '71299/40000', '3', '43/20', '257/100'),
     ('17/32', '171/320', '33/80', '67/160', '1792189/1000000', '3', '43/20', '51/20'),
     ('17/32', '171/320', '67/160', '17/40', '895437/500000', '3', '43/20', '259/100'),
     ('171/320', '43/80', '33/80', '67/160', '1781821/1000000', '3', '43/20', '261/100'),
     ('171/320', '343/640', '67/160', '27/64', '445159/250000', '3', '43/20', '257/100'),
     ('171/320', '343/640', '27/64', '17/40', '889923/500000', '3', '43/20', '259/100'),
     ('343/640', '43/80', '67/160', '27/64', '887717/500000', '3', '43/20', '259/100'),
     ('343/640', '43/80', '27/64', '17/40', '70987/40000', '3', '43/20', '261/100'),
     ('21/40', '673/1280', '17/40', '273/640', '452141/250000', '3', '11/5', '131/50'),
     ('21/40', '673/1280', '273/640', '137/320', '903979/500000', '3', '11/5', '66/25'),
     ('673/1280', '337/640', '17/40', '273/640', '903087/500000', '3', '43/20', '249/100'),
     ('673/1280', '337/640', '273/640', '137/320', '225697/125000', '3', '43/20', '249/100'),
     ('21/40', '673/1280', '137/320', '55/128', '1807319/1000000', '3', '43/20', '249/100'),
     ('21/40', '673/1280', '55/128', '69/160', '1806649/1000000', '3', '43/20', '249/100'),
     ('673/1280', '337/640', '137/320', '55/128', '360989/200000', '3', '43/20', '249/100'),
     ('673/1280', '337/640', '55/128', '69/160', '1804283/1000000', '3', '43/20', '249/100'),
     ('337/640', '169/320', '17/40', '137/320', '1803769/1000000', '3', '43/20', '251/100'),
     ('337/640', '169/320', '137/320', '69/160', '1802557/1000000', '3', '43/20', '251/100'),
     ('21/40', '673/1280', '69/160', '277/640', '902973/500000', '3', '43/20', '249/100'),
     ('21/40', '673/1280', '277/640', '139/320', '1804221/1000000', '5', '43/20', '249/100'),
     ('673/1280', '337/640', '69/160', '277/640', '450897/250000', '3', '43/20', '251/100'),
     ('673/1280', '337/640', '277/640', '139/320', '1802861/1000000', '3', '43/20', '251/100'),
     ('21/40', '337/640', '139/320', '7/16', '360181/200000', '5', '43/20', '251/100'),
     ('337/640', '169/320', '69/160', '139/320', '360243/200000', '3', '43/20', '251/100'),
     ('337/640', '169/320', '139/320', '7/16', '359713/200000', '5', '43/20', '253/100'),
     ('169/320', '339/640', '17/40', '137/320', '359783/200000', '3', '43/20', '251/100'),
     ('169/320', '339/640', '137/320', '69/160', '359547/200000', '3', '43/20', '253/100'),
     ('339/640', '17/32', '17/40', '137/320', '1794003/1000000', '3', '43/20', '253/100'),
     ('339/640', '17/32', '137/320', '69/160', '358571/200000', '3', '43/20', '51/20'),
     ('169/320', '339/640', '69/160', '139/320', '898213/500000', '3', '43/20', '253/100'),
     ('169/320', '339/640', '139/320', '7/16', '1794987/1000000', '3', '43/20', '51/20'),
     ('339/640', '17/32', '69/160', '139/320', '1791577/1000000', '3', '43/20', '257/100'),
     ('339/640', '17/32', '139/320', '7/16', '179017/100000', '3', '43/20', '257/100'),
     ('21/40', '169/320', '7/16', '71/160', '1793949/1000000', '5', '43/20', '51/20'),
     ('21/40', '169/320', '71/160', '9/20', '17787/10000', '5', '43/20', '253/100'),
     ('169/320', '339/640', '7/16', '141/320', '357881/200000', '5', '43/20', '51/20'),
     ('169/320', '339/640', '141/320', '71/160', '891091/500000', '5', '43/20', '51/20'),
     ('339/640', '17/32', '7/16', '141/320', '1787077/1000000', '5', '43/20', '259/100'),
     ('339/640', '17/32', '141/320', '71/160', '889971/500000', '5', '43/20', '259/100'),
     ('169/320', '17/32', '71/160', '9/20', '1774509/1000000', '5', '43/20', '261/100'),
     ('17/32', '341/640', '17/40', '137/320', '1789033/1000000', '3', '43/20', '51/20'),
     ('17/32', '341/640', '137/320', '69/160', '1787917/1000000', '3', '43/20', '257/100'),
     ('341/640', '171/320', '17/40', '137/320', '1784007/1000000', '3', '43/20', '259/100'),
     ('341/640', '171/320', '137/320', '69/160', '891461/500000', '3', '43/20', '259/100'),
     ('17/32', '341/640', '69/160', '139/320', '1786671/1000000', '3', '43/20', '259/100'),
     ('17/32', '341/640', '139/320', '7/16', '357059/200000', '3', '43/20', '261/100'),
     ('341/640', '171/320', '69/160', '139/320', '1781707/1000000', '3', '43/20', '261/100'),
     ('341/640', '171/320', '139/320', '7/16', '890181/500000', '3', '43/20', '263/100'),
     ('171/320', '343/640', '17/40', '137/320', '1778923/1000000', '3', '43/20', '261/100'),
     ('171/320', '343/640', '137/320', '69/160', '177787/100000', '3', '43/20', '263/100'),
     ('343/640', '43/80', '17/40', '137/320', '221723/125000', '3', '43/20', '263/100'),
     ('343/640', '43/80', '137/320', '69/160', '1772761/1000000', '3', '17/8', '51/20'),
     ('171/320', '343/640', '69/160', '139/320', '888343/500000', '3', '43/20', '263/100'),
     ('171/320', '343/640', '139/320', '7/16', '1775371/1000000', '3', '17/8', '51/20'),
     ('343/640', '43/80', '69/160', '139/320', '221451/125000', '3', '17/8', '51/20'),
     ('343/640', '43/80', '139/320', '7/16', '442581/250000', '3', '17/8', '257/100'),
     ('17/32', '341/640', '7/16', '141/320', '178379/100000', '3', '43/20', '261/100'),
     ('17/32', '341/640', '141/320', '71/160', '888833/500000', '5', '43/20', '261/100'),
     ('341/640', '683/1280', '7/16', '281/640', '222361/125000', '3', '43/20', '261/100'),
     ('341/640', '683/1280', '281/640', '141/320', '889051/500000', '3', '43/20', '261/100'),
     ('683/1280', '171/320', '7/16', '281/640', '355283/200000', '3', '43/20', '263/100'),
     ('683/1280', '171/320', '281/640', '141/320', '1775637/1000000', '3', '43/20', '263/100'),
     ('341/640', '171/320', '141/320', '71/160', '887677/500000', '5', '43/20', '53/20'),
     ('17/32', '171/320', '71/160', '9/20', '1770171/1000000', '5', '17/8', '51/20'),
     ('171/320', '137/256', '7/16', '281/640', '1773927/1000000', '3', '43/20', '263/100'),
     ('171/320', '137/256', '281/640', '141/320', '1773157/1000000', '3', '43/20', '53/20'),
     ('137/256', '343/640', '7/16', '281/640', '885713/500000', '3', '43/20', '53/20'),
     ('137/256', '343/640', '281/640', '141/320', '1770663/1000000', '3', '17/8', '51/20'),
     ('171/320', '137/256', '141/320', '283/640', '886177/500000', '3', '17/8', '51/20'),
     ('171/320', '137/256', '283/640', '71/160', '884703/500000', '5', '43/20', '53/20'),
     ('137/256', '343/640', '141/320', '283/640', '1769867/1000000', '3', '17/8', '51/20'),
     ('137/256', '343/640', '283/640', '71/160', '884121/500000', '5', '17/8', '257/100'),
     ('343/640', '43/80', '7/16', '141/320', '176891/100000', '3', '17/8', '259/100'),
     ('343/640', '43/80', '141/320', '71/160', '883683/500000', '3', '17/8', '261/100'),
     ('171/320', '343/640', '71/160', '143/320', '441423/250000', '5', '17/8', '257/100'),
     ('171/320', '343/640', '143/320', '9/20', '1757919/1000000', '5', '17/8', '257/100'),
     ('343/640', '43/80', '71/160', '143/320', '8817/5000', '5', '17/8', '261/100'),
     ('343/640', '43/80', '143/320', '9/20', '877859/500000', '5', '17/8', '261/100'),
     ('21/40', '169/320', '9/20', '73/160', '440403/250000', '5', '43/20', '253/100'),
     ('21/40', '169/320', '73/160', '37/80', '871309/500000', '5', '43/20', '251/100'),
     ('169/320', '17/32', '9/20', '73/160', '878889/500000', '5', '43/20', '259/100'),
     ('169/320', '17/32', '73/160', '37/80', '1739141/1000000', '5', '43/20', '257/100'),
     ('21/40', '169/320', '37/80', '15/32', '344329/200000', '5', '43/20', '251/100'),
     ('21/40', '169/320', '15/32', '19/40', '1698623/1000000', '5', '11/5', '131/50'),
     ('169/320', '17/32', '37/80', '15/32', '1718529/1000000', '5', '43/20', '51/20'),
     ('169/320', '17/32', '15/32', '19/40', '169587/100000', '5', '43/20', '253/100'),
     ('17/32', '171/320', '9/20', '73/160', '1753799/1000000', '5', '17/8', '51/20'),
     ('17/32', '171/320', '73/160', '37/80', '1735523/1000000', '5', '43/20', '263/100'),
     ('171/320', '43/80', '9/20', '73/160', '21871/12500', '5', '17/8', '263/100'),
     ('171/320', '43/80', '73/160', '37/80', '216471/125000', '5', '17/8', '261/100'),
     ('17/32', '171/320', '37/80', '15/32', '857637/500000', '5', '43/20', '261/100'),
     ('17/32', '171/320', '15/32', '19/40', '84649/50000', '5', '43/20', '259/100'),
     ('171/320', '43/80', '37/80', '15/32', '427971/250000', '5', '17/8', '259/100'),
     ('171/320', '43/80', '15/32', '19/40', '844979/500000', '5', '17/8', '51/20'),
     ('21/40', '169/320', '19/40', '77/160', '836741/500000', '5', '11/5', '13/5'),
     ('21/40', '169/320', '77/160', '39/80', '411537/250000', '5', '11/5', '64/25'),
     ('169/320', '17/32', '19/40', '77/160', '417773/250000', '5', '43/20', '251/100'),
     ('169/320', '17/32', '77/160', '39/80', '1644123/1000000', '5', '43/20', '249/100'),
     ('21/40', '17/32', '39/80', '1/2', '32331/20000', '5', '11/5', '131/50'),
     ('17/32', '171/320', '19/40', '77/160', '1668569/1000000', '5', '43/20', '51/20'),
     ('17/32', '171/320', '77/160', '39/80', '102623/62500', '5', '43/20', '253/100'),
     ('171/320', '43/80', '19/40', '77/160', '416479/250000', '5', '43/20', '261/100'),
     ('171/320', '43/80', '77/160', '39/80', '1639687/1000000', '5', '43/20', '259/100'),
     ('17/32', '171/320', '39/80', '79/160', '322621/200000', '5', '43/20', '249/100'),
     ('17/32', '171/320', '79/160', '1/2', '347039/200000', '3', '21/10', '263/100'),
     ('171/320', '43/80', '39/80', '79/160', '402799/250000', '5', '43/20', '51/20'),
     ('171/320', '43/80', '79/160', '1/2', '1580369/1000000', '5', '43/20', '251/100'),
     ('21/40', '169/320', '1/2', '81/160', '775133/500000', '5', '11/5', '61/25'),
     ('21/40', '169/320', '81/160', '41/80', '867769/500000', '3', '17/8', '53/20'),
     ('169/320', '17/32', '1/2', '81/160', '1549343/1000000', '5', '11/5', '5/2'),
     ('169/320', '17/32', '81/160', '41/80', '345487/200000', '3', '21/10', '261/100'),
     ('21/40', '17/32', '41/80', '21/40', '1726559/1000000', '3', '21/10', '53/20'),
     ('17/32', '171/320', '1/2', '81/160', '1548297/1000000', '5', '11/5', '64/25'),
     ('17/32', '171/320', '81/160', '41/80', '1719061/1000000', '3', '21/10', '267/100'),
     ('171/320', '43/80', '1/2', '81/160', '773567/500000', '5', '43/20', '249/100'),
     ('171/320', '43/80', '81/160', '41/80', '85521/50000', '3', '21/10', '271/100'),
     ('17/32', '171/320', '41/80', '83/160', '855149/500000', '3', '21/10', '267/100'),
     ('17/32', '171/320', '83/160', '21/40', '42527/25000', '3', '21/10', '267/100'),
     ('171/320', '43/80', '41/80', '83/160', '1701759/1000000', '3', '21/10', '271/100'),
     ('171/320', '43/80', '83/160', '21/40', '1692641/1000000', '3', '21/10', '273/100'),
     ('21/40', '17/32', '21/40', '17/32', '341449/200000', '3', '21/10', '53/20'),
     ('17/32', '43/80', '21/40', '17/32', '422853/250000', '3', '83/40', '53/20'),
     ('17/32', '43/80', '17/32', '43/80', '1681303/1000000', '3', '83/40', '267/100'),
     ('43/80', '11/20', '79507/512000', '7/40', '23863/15625', '4', '5/2', '199/100'),
     ('43/80', '11/20', '7/40', '1/5', '1563577/1000000', '4', '5/2', '43/20'),
     ('43/80', '11/20', '1/5', '9/40', '1597799/1000000', '4', '12/5', '211/100'),
     ('43/80', '11/20', '9/40', '1/4', '1629981/1000000', '4', '12/5', '233/100'),
     ('43/80', '11/20', '1/4', '11/40', '1654403/1000000', '3', '23/10', '56/25'),
     ('43/80', '11/20', '11/40', '3/10', '422147/250000', '4', '9/4', '58/25'),
     ('43/80', '11/20', '3/10', '13/40', '857613/500000', '4', '9/4', '5/2'),
     ('43/80', '11/20', '13/40', '7/20', '1740251/1000000', '4', '11/5', '127/50'),
     ('43/80', '11/20', '7/20', '3/8', '352761/200000', '4', '43/20', '257/100'),
     ('43/80', '87/160', '3/8', '31/80', '1770091/1000000', '3', '43/20', '253/100'),
     ('43/80', '87/160', '31/80', '2/5', '1771743/1000000', '3', '43/20', '261/100'),
     ('87/160', '11/20', '3/8', '31/80', '1747219/1000000', '3', '17/8', '253/100'),
     ('87/160', '11/20', '31/80', '2/5', '1749411/1000000', '3', '17/8', '261/100'),
     ('43/80', '87/160', '2/5', '33/80', '1771861/1000000', '3', '17/8', '259/100'),
     ('43/80', '173/320', '33/80', '67/160', '885617/500000', '3', '17/8', '51/20'),
     ('43/80', '173/320', '67/160', '17/40', '1770177/1000000', '3', '17/8', '257/100'),
     ('173/320', '87/160', '33/80', '67/160', '1760431/1000000', '3', '17/8', '259/100'),
     ('173/320', '87/160', '67/160', '17/40', '3519/2000', '3', '17/8', '263/100'),
     ('87/160', '11/20', '2/5', '33/80', '87487/50000', '3', '21/10', '257/100'),
     ('87/160', '35/64', '33/80', '67/160', '874709/500000', '3', '17/8', '263/100'),
     ('87/160', '35/64', '67/160', '17/40', '174861/100000', '3', '21/10', '257/100'),
     ('35/64', '11/20', '33/80', '67/160', '869099/500000', '3', '21/10', '257/100'),
     ('35/64', '11/20', '67/160', '17/40', '217189/125000', '3', '21/10', '261/100'),
     ('43/80', '69/128', '17/40', '137/320', '1768589/1000000', '3', '17/8', '51/20'),
     ('43/80', '69/128', '137/320', '69/160', '1767597/1000000', '3', '17/8', '257/100'),
     ('69/128', '173/320', '17/40', '137/320', '1763339/1000000', '3', '17/8', '257/100'),
     ('69/128', '173/320', '137/320', '69/160', '881189/500000', '3', '17/8', '259/100'),
     ('43/80', '69/128', '69/160', '139/320', '883237/500000', '3', '17/8', '259/100'),
     ('43/80', '69/128', '139/320', '7/16', '88261/50000', '3', '17/8', '259/100'),
     ('69/128', '173/320', '69/160', '139/320', '352257/200000', '3', '17/8', '261/100'),
     ('69/128', '173/320', '139/320', '7/16', '1760061/1000000', '3', '17/8', '263/100'),
     ('173/320', '347/640', '17/40', '137/320', '351607/200000', '3', '17/8', '261/100'),
     ('173/320', '347/640', '137/320', '69/160', '109819/62500', '3', '17/8', '261/100'),
     ('347/640', '87/160', '17/40', '137/320', '1752677/1000000', '3', '17/8', '263/100'),
     ('347/640', '87/160', '137/320', '69/160', '54743/31250', '3', '17/8', '53/20'),
     ('173/320', '347/640', '69/160', '139/320', '1756041/1000000', '3', '17/8', '263/100'),
     ('173/320', '347/640', '139/320', '7/16', '877423/500000', '3', '17/8', '53/20'),
     ('347/640', '87/160', '69/160', '139/320', '875371/500000', '3', '17/8', '53/20'),
     ('347/640', '87/160', '139/320', '7/16', '1749577/1000000', '3', '17/8', '267/100'),
     ('43/80', '69/128', '7/16', '141/320', '440959/250000', '3', '17/8', '261/100'),
     ('43/80', '69/128', '141/320', '71/160', '881161/500000', '3', '17/8', '263/100'),
     ('69/128', '173/320', '7/16', '141/320', '879353/500000', '3', '17/8', '263/100'),
     ('69/128', '173/320', '141/320', '71/160', '1757221/1000000', '3', '17/8', '53/20'),
     ('43/80', '689/1280', '71/160', '57/128', '1760679/1000000', '3', '17/8', '261/100'),
     ('43/80', '689/1280', '57/128', '143/320', '1757337/1000000', '5', '17/8', '261/100'),
     ('689/1280', '69/128', '71/160', '57/128', '35163/20000', '3', '17/8', '263/100'),
     ('689/1280', '69/128', '57/128', '143/320', '351237/200000', '5', '17/8', '263/100'),
     ('43/80', '69/128', '143/320', '9/20', '438371/250000', '5', '17/8', '263/100'),
     ('69/128', '691/1280', '71/160', '57/128', '1755607/1000000', '3', '17/8', '263/100'),
     ('69/128', '691/1280', '57/128', '143/320', '1754751/1000000', '3', '17/8', '53/20'),
     ('691/1280', '173/320', '71/160', '57/128', '35061/20000', '3', '17/8', '53/20'),
     ('691/1280', '173/320', '57/128', '143/320', '1752201/1000000', '3', '17/8', '53/20'),
     ('69/128', '173/320', '143/320', '9/20', '109451/62500', '5', '17/8', '267/100'),
     ('173/320', '347/640', '7/16', '141/320', '21919/12500', '3', '17/8', '267/100'),
     ('173/320', '693/1280', '141/320', '283/640', '27376/15625', '3', '17/8', '53/20'),
     ('173/320', '693/1280', '283/640', '71/160', '218911/125000', '3', '17/8', '53/20'),
     ('693/1280', '347/640', '141/320', '283/640', '349893/200000', '3', '17/8', '53/20'),
     ('693/1280', '347/640', '283/640', '71/160', '218587/125000', '3', '17/8', '267/100'),
     ('347/640', '87/160', '7/16', '141/320', '43707/25000', '3', '21/10', '257/100'),
     ('347/640', '87/160', '141/320', '71/160', '1746853/1000000', '3', '21/10', '259/100'),
     ('173/320', '693/1280', '71/160', '57/128', '875239/500000', '3', '17/8', '53/20'),
     ('173/320', '693/1280', '57/128', '143/320', '1749637/1000000', '3', '17/8', '267/100'),
     ('693/1280', '347/640', '71/160', '57/128', '873947/500000', '3', '17/8', '267/100'),
     ('693/1280', '347/640', '57/128', '143/320', '1747059/1000000', '3', '17/8', '267/100'),
     ('173/320', '693/1280', '143/320', '287/640', '1748763/1000000', '3', '17/8', '267/100'),
     ('173/320', '693/1280', '287/640', '9/20', '1745039/1000000', '5', '17/8', '267/100'),
     ('693/1280', '347/640', '143/320', '287/640', '109137/62500', '3', '21/10', '257/100'),
     ('693/1280', '347/640', '287/640', '9/20', '1743901/1000000', '5', '21/10', '259/100'),
     ('347/640', '87/160', '71/160', '143/320', '349059/200000', '3', '21/10', '261/100'),
     ('347/640', '139/256', '143/320', '287/640', '1743607/1000000', '3', '21/10', '259/100'),
     ('347/640', '139/256', '287/640', '9/20', '348543/200000', '3', '21/10', '259/100'),
     ('139/256', '87/160', '143/320', '287/640', '1741009/1000000', '3', '21/10', '261/100'),
     ('139/256', '87/160', '287/640', '9/20', '435031/250000', '3', '21/10', '261/100'),
     ('87/160', '35/64', '17/40', '69/160', '873633/500000', '3', '21/10', '261/100'),
     ('87/160', '349/640', '69/160', '139/320', '174539/100000', '3', '21/10', '257/100'),
     ('87/160', '349/640', '139/320', '7/16', '872127/500000', '3', '21/10', '259/100'),
     ('349/640', '35/64', '69/160', '139/320', '347997/200000', '3', '21/10', '259/100'),
     ('349/640', '35/64', '139/320', '7/16', '1738877/1000000', '3', '21/10', '261/100'),
     ('35/64', '11/20', '17/40', '69/160', '54259/31250', '3', '21/10', '53/20'),
     ('35/64', '351/640', '69/160', '139/320', '27102/15625', '3', '21/10', '263/100'),
     ('35/64', '351/640', '139/320', '7/16', '216681/125000', '3', '21/10', '263/100'),
     ('351/640', '11/20', '69/160', '139/320', '1729019/1000000', '3', '21/10', '53/20'),
     ('351/640', '11/20', '139/320', '7/16', '53999/31250', '3', '21/10', '267/100'),
     ('87/160', '349/640', '7/16', '141/320', '871493/500000', '3', '21/10', '261/100'),
     ('87/160', '349/640', '141/320', '71/160', '870793/500000', '3', '21/10', '261/100'),
     ('349/640', '35/64', '7/16', '141/320', '868819/500000', '3', '21/10', '263/100'),
     ('349/640', '35/64', '141/320', '71/160', '868133/500000', '3', '21/10', '53/20'),
     ('87/160', '349/640', '71/160', '143/320', '1740057/1000000', '3', '21/10', '263/100'),
     ('87/160', '349/640', '143/320', '9/20', '1738397/1000000', '3', '21/10', '53/20'),
     ('349/640', '35/64', '71/160', '143/320', '433691/250000', '3', '21/10', '53/20'),
     ('349/640', '35/64', '143/320', '9/20', '433283/250000', '3', '21/10', '267/100'),
     ('35/64', '351/640', '7/16', '141/320', '1732237/1000000', '3', '21/10', '53/20'),
     ('35/64', '351/640', '141/320', '71/160', '1730893/1000000', '3', '21/10', '267/100'),
     ('351/640', '11/20', '7/16', '141/320', '1726783/1000000', '3', '21/10', '267/100'),
     ('351/640', '11/20', '141/320', '71/160', '1725467/1000000', '3', '21/10', '269/100'),
     ('35/64', '351/640', '71/160', '143/320', '864709/500000', '3', '21/10', '269/100'),
     ('35/64', '351/640', '143/320', '9/20', '1727813/1000000', '3', '21/10', '269/100'),
     ('351/640', '11/20', '71/160', '143/320', '1724019/1000000', '3', '21/10', '271/100'),
     ('351/640', '11/20', '143/320', '9/20', '43061/25000', '3', '83/40', '261/100'),
     ('43/80', '173/320', '9/20', '73/160', '1745427/1000000', '5', '17/8', '269/100'),
     ('43/80', '173/320', '73/160', '37/80', '43197/25000', '5', '17/8', '267/100'),
     ('173/320', '347/640', '9/20', '29/64', '435261/250000', '5', '21/10', '259/100'),
     ('173/320', '347/640', '29/64', '73/160', '216587/125000', '5', '21/10', '259/100'),
     ('347/640', '87/160', '9/20', '29/64', '869403/500000', '5', '21/10', '263/100'),
     ('347/640', '87/160', '29/64', '73/160', '1730551/1000000', '5', '21/10', '261/100'),
     ('173/320', '87/160', '73/160', '37/80', '861933/500000', '5', '21/10', '263/100'),
     ('43/80', '173/320', '37/80', '15/32', '341673/200000', '5', '17/8', '53/20'),
     ('43/80', '173/320', '15/32', '19/40', '1686809/1000000', '5', '17/8', '263/100'),
     ('173/320', '87/160', '37/80', '15/32', '852361/500000', '5', '21/10', '261/100'),
     ('173/320', '87/160', '15/32', '19/40', '1683539/1000000', '5', '21/10', '259/100'),
     ('87/160', '697/1280', '9/20', '289/640', '1736537/1000000', '5', '21/10', '263/100'),
     ('87/160', '697/1280', '289/640', '29/64', '433129/250000', '5', '21/10', '263/100'),
     ('697/1280', '349/640', '9/20', '289/640', '346799/200000', '3', '21/10', '53/20'),
     ('697/1280', '349/640', '289/640', '29/64', '865697/500000', '5', '21/10', '53/20'),
     ('87/160', '349/640', '29/64', '73/160', '13827/8000', '5', '21/10', '53/20'),
     ('349/640', '699/1280', '9/20', '289/640', '1731369/1000000', '3', '21/10', '53/20'),
     ('349/640', '699/1280', '289/640', '29/64', '346053/200000', '5', '21/10', '53/20'),
     ('699/1280', '35/64', '9/20', '289/640', '172873/100000', '3', '21/10', '267/100'),
     ('699/1280', '35/64', '289/640', '29/64', '1727807/1000000', '3', '21/10', '267/100'),
     ('349/640', '35/64', '29/64', '73/160', '1726171/1000000', '5', '21/10', '269/100'),
     ('87/160', '35/64', '73/160', '37/80', '1719731/1000000', '5', '21/10', '271/100'),
     ('35/64', '351/640', '9/20', '29/64', '1726077/1000000', '3', '21/10', '271/100'),
     ('35/64', '701/1280', '29/64', '291/640', '861969/500000', '5', '21/10', '269/100'),
     ('35/64', '701/1280', '291/640', '73/160', '171977/100000', '5', '21/10', '269/100'),
     ('701/1280', '351/640', '29/64', '291/640', '860779/500000', '3', '21/10', '271/100'),
     ('701/1280', '351/640', '291/640', '73/160', '1718667/1000000', '5', '21/10', '271/100'),
     ('351/640', '11/20', '9/20', '29/64', '1720731/1000000', '3', '83/40', '263/100'),
     ('351/640', '11/20', '29/64', '73/160', '1718891/1000000', '3', '83/40', '263/100'),
     ('35/64', '351/640', '73/160', '147/320', '1715481/1000000', '5', '21/10', '271/100'),
     ('35/64', '351/640', '147/320', '37/80', '853267/500000', '5', '21/10', '271/100'),
     ('351/640', '11/20', '73/160', '147/320', '856657/500000', '5', '83/40', '263/100'),
     ('351/640', '11/20', '147/320', '37/80', '852231/500000', '5', '83/40', '263/100'),
     ('87/160', '35/64', '37/80', '15/32', '1700961/1000000', '5', '21/10', '269/100'),
     ('87/160', '35/64', '15/32', '19/40', '1680153/1000000', '5', '21/10', '53/20'),
     ('35/64', '11/20', '37/80', '15/32', '1697087/1000000', '5', '83/40', '53/20'),
     ('35/64', '11/20', '15/32', '19/40', '838329/500000', '5', '83/40', '263/100'),
     ('43/80', '173/320', '19/40', '77/160', '83157/50000', '5', '17/8', '259/100'),
     ('43/80', '173/320', '77/160', '39/80', '1637283/1000000', '5', '17/8', '257/100'),
     ('173/320', '87/160', '19/40', '77/160', '415061/250000', '5', '17/8', '53/20'),
     ('173/320', '87/160', '77/160', '39/80', '408691/250000', '5', '17/8', '263/100'),
     ('43/80', '173/320', '39/80', '79/160', '1609167/1000000', '5', '43/20', '261/100'),
     ('43/80', '173/320', '79/160', '1/2', '1578717/1000000', '5', '43/20', '257/100'),
     ('173/320', '87/160', '39/80', '79/160', '803513/500000', '5', '17/8', '259/100'),
     ('173/320', '87/160', '79/160', '1/2', '1576953/1000000', '5', '17/8', '51/20'),
     ('87/160', '35/64', '19/40', '77/160', '414309/250000', '5', '21/10', '263/100'),
     ('87/160', '35/64', '77/160', '39/80', '326427/200000', '5', '21/10', '259/100'),
     ('35/64', '11/20', '19/40', '77/160', '1654121/1000000', '5', '21/10', '269/100'),
     ('35/64', '11/20', '77/160', '39/80', '814701/500000', '5', '21/10', '267/100'),
     ('87/160', '35/64', '39/80', '79/160', '200597/125000', '5', '17/8', '53/20'),
     ('87/160', '35/64', '79/160', '1/2', '315017/200000', '5', '17/8', '261/100'),
     ('35/64', '11/20', '39/80', '79/160', '801213/500000', '5', '21/10', '263/100'),
     ('35/64', '11/20', '79/160', '1/2', '786559/500000', '5', '21/10', '259/100'),
     ('43/80', '173/320', '1/2', '81/160', '1545857/1000000', '5', '43/20', '253/100'),
     ('43/80', '173/320', '81/160', '41/80', '850757/500000', '3', '83/40', '267/100'),
     ('173/320', '87/160', '1/2', '81/160', '193059/125000', '5', '43/20', '259/100'),
     ('173/320', '87/160', '81/160', '41/80', '33847/20000', '3', '83/40', '271/100'),
     ('43/80', '173/320', '41/80', '83/160', '1692951/1000000', '3', '83/40', '267/100'),
     ('43/80', '173/320', '83/160', '21/40', '1683931/1000000', '3', '83/40', '267/100'),
     ('173/320', '87/160', '41/80', '83/160', '42097/25000', '3', '83/40', '273/100'),
     ('173/320', '87/160', '83/160', '21/40', '209369/125000', '3', '83/40', '273/100'),
     ('87/160', '35/64', '1/2', '81/160', '308597/200000', '5', '17/8', '257/100'),
     ('87/160', '35/64', '81/160', '41/80', '168293/100000', '3', '83/40', '277/100'),
     ('35/64', '11/20', '1/2', '81/160', '1541403/1000000', '5', '17/8', '263/100'),
     ('35/64', '11/20', '81/160', '41/80', '83663/50000', '3', '41/20', '68/25'),
     ('87/160', '35/64', '41/80', '83/160', '33491/20000', '3', '83/40', '277/100'),
     ('87/160', '35/64', '83/160', '21/40', '1665709/1000000', '3', '41/20', '67/25'),
     ('35/64', '11/20', '41/80', '83/160', '332993/200000', '3', '41/20', '68/25'),
     ('35/64', '11/20', '83/160', '21/40', '1656207/1000000', '3', '41/20', '68/25'),
     ('43/80', '87/160', '21/40', '43/80', '1674459/1000000', '3', '83/40', '277/100'),
     ('43/80', '87/160', '43/80', '87/160', '103387/62500', '3', '83/40', '11/4'),
     ('87/160', '11/20', '21/40', '43/80', '828207/500000', '3', '41/20', '139/50'),
     ('87/160', '11/20', '43/80', '11/20', '327299/200000', '3', '41/20', '139/50'),
     ('11/20', '9/16', '1331/8000', '7/40', '1463273/1000000', '4', '5/2', '41/20'),
     ('11/20', '9/16', '7/40', '1/5', '1501087/1000000', '4', '12/5', '209/100'),
     ('11/20', '9/16', '1/5', '9/40', '1536659/1000000', '4', '12/5', '223/100'),
     ('11/20', '9/16', '9/40', '1/4', '196259/125000', '4', '23/10', '111/50'),
     ('11/20', '9/16', '1/4', '11/40', '1595943/1000000', '3', '23/10', '59/25'),
     ('11/20', '9/16', '11/40', '3/10', '815403/500000', '4', '9/4', '121/50'),
     ('11/20', '9/16', '3/10', '13/40', '414587/250000', '4', '11/5', '123/50'),
     ('11/20', '9/16', '13/40', '7/20', '84209/50000', '4', '43/20', '249/100'),
     ('11/20', '9/16', '7/20', '3/8', '34169/20000', '4', '17/8', '261/100'),
     ('11/20', '89/160', '3/8', '31/80', '860027/500000', '4', '17/8', '259/100'),
     ('11/20', '89/160', '31/80', '2/5', '1726271/1000000', '3', '21/10', '259/100'),
     ('89/160', '9/16', '3/8', '31/80', '845597/500000', '4', '21/10', '51/20'),
     ('89/160', '9/16', '31/80', '2/5', '851183/500000', '3', '21/10', '267/100'),
     ('11/20', '89/160', '2/5', '33/80', '863451/500000', '3', '21/10', '53/20'),
     ('11/20', '177/320', '33/80', '67/160', '1726779/1000000', '3', '21/10', '263/100'),
     ('11/20', '177/320', '67/160', '17/40', '1726213/1000000', '3', '21/10', '267/100'),
     ('177/320', '89/160', '33/80', '67/160', '343033/200000', '3', '21/10', '267/100'),
     ('177/320', '89/160', '67/160', '17/40', '1714717/1000000', '3', '21/10', '271/100'),
     ('89/160', '9/16', '2/5', '33/80', '1703381/1000000', '3', '83/40', '263/100'),
     ('89/160', '9/16', '33/80', '17/40', '1703363/1000000', '3', '83/40', '271/100'),
     ('11/20', '177/320', '17/40', '69/160', '345021/200000', '3', '21/10', '269/100'),
     ('11/20', '353/640', '69/160', '139/320', '1723459/1000000', '3', '21/10', '267/100'),
     ('11/20', '353/640', '139/320', '7/16', '430609/250000', '3', '21/10', '269/100'),
     ('353/640', '177/320', '69/160', '139/320', '1717849/1000000', '3', '21/10', '269/100'),
     ('353/640', '177/320', '139/320', '7/16', '1716853/1000000', '3', '21/10', '271/100'),
     ('177/320', '89/160', '17/40', '69/160', '428431/250000', '3', '83/40', '263/100'),
     ('177/320', '89/160', '69/160', '7/16', '171219/100000', '3', '83/40', '267/100'),
     ('11/20', '353/640', '7/16', '141/320', '1721279/1000000', '3', '21/10', '269/100'),
     ('11/20', '353/640', '141/320', '71/160', '171999/100000', '3', '21/10', '271/100'),
     ('353/640', '177/320', '7/16', '141/320', '428931/250000', '3', '83/40', '261/100'),
     ('353/640', '177/320', '141/320', '71/160', '1714461/1000000', '3', '83/40', '263/100'),
     ('11/20', '353/640', '71/160', '143/320', '1718569/1000000', '3', '83/40', '261/100'),
     ('11/20', '353/640', '143/320', '9/20', '214627/125000', '3', '83/40', '263/100'),
     ('353/640', '177/320', '71/160', '143/320', '856533/500000', '3', '83/40', '53/20'),
     ('353/640', '177/320', '143/320', '9/20', '85577/50000', '3', '83/40', '53/20'),
     ('177/320', '89/160', '7/16', '71/160', '855059/500000', '3', '83/40', '269/100'),
     ('177/320', '71/128', '71/160', '143/320', '853757/500000', '3', '83/40', '267/100'),
     ('177/320', '71/128', '143/320', '9/20', '1706013/1000000', '3', '83/40', '269/100'),
     ('71/128', '89/160', '71/160', '143/320', '1701911/1000000', '3', '83/40', '269/100'),
     ('71/128', '89/160', '143/320', '9/20', '425109/250000', '3', '83/40', '271/100'),
     ('89/160', '179/320', '17/40', '69/160', '1702151/1000000', '3', '83/40', '267/100'),
     ('89/160', '179/320', '69/160', '7/16', '850363/500000', '3', '83/40', '271/100'),
     ('179/320', '9/16', '17/40', '69/160', '1690391/1000000', '3', '83/40', '273/100'),
     ('179/320', '9/16', '69/160', '7/16', '844537/500000', '3', '41/20', '66/25'),
     ('89/160', '179/320', '7/16', '71/160', '1698761/1000000', '3', '83/40', '11/4'),
     ('89/160', '357/640', '71/160', '143/320', '84813/50000', '3', '83/40', '271/100'),
     ('89/160', '357/640', '143/320', '9/20', '1694809/1000000', '3', '83/40', '273/100'),
     ('357/640', '179/320', '71/160', '143/320', '5283/3125', '3', '83/40', '273/100'),
     ('357/640', '179/320', '143/320', '9/20', '337827/200000', '3', '83/40', '11/4'),
     ('179/320', '9/16', '7/16', '71/160', '843607/500000', '3', '41/20', '67/25'),
     ('179/320', '9/16', '71/160', '9/20', '1684813/1000000', '3', '41/20', '27/10'),
     ('11/20', '353/640', '9/20', '29/64', '428833/250000', '3', '83/40', '53/20'),
     ('11/20', '353/640', '29/64', '73/160', '1713519/1000000', '3', '83/40', '53/20'),
     ('353/640', '177/320', '9/20', '29/64', '854941/500000', '3', '83/40', '267/100'),
     ('353/640', '177/320', '29/64', '73/160', '1708093/1000000', '3', '83/40', '269/100'),
     ('11/20', '353/640', '73/160', '147/320', '855561/500000', '5', '83/40', '267/100'),
     ('11/20', '353/640', '147/320', '37/80', '425591/250000', '5', '83/40', '267/100'),
     ('353/640', '177/320', '73/160', '147/320', '68247/40000', '3', '83/40', '269/100'),
     ('353/640', '177/320', '147/320', '37/80', '1700241/1000000', '5', '83/40', '269/100'),
     ('177/320', '71/128', '9/20', '29/64', '85219/50000', '3', '83/40', '269/100'),
     ('177/320', '71/128', '29/64', '73/160', '1702617/1000000', '3', '83/40', '271/100'),
     ('71/128', '89/160', '9/20', '29/64', '424707/250000', '3', '83/40', '271/100'),
     ('71/128', '89/160', '29/64', '73/160', '1697089/1000000', '3', '83/40', '273/100'),
     ('177/320', '71/128', '73/160', '147/320', '1700723/1000000', '3', '83/40', '271/100'),
     ('177/320', '71/128', '147/320', '37/80', '849047/500000', '5', '83/40', '273/100'),
     ('71/128', '89/160', '73/160', '147/320', '1695219/1000000', '3', '83/40', '11/4'),
     ('71/128', '89/160', '147/320', '37/80', '1693219/1000000', '3', '83/40', '11/4'),
     ('11/20', '177/320', '37/80', '15/32', '1693107/1000000', '5', '83/40', '271/100'),
     ('11/20', '177/320', '15/32', '19/40', '83653/50000', '5', '83/40', '269/100'),
     ('177/320', '89/160', '37/80', '15/32', '422257/250000', '5', '41/20', '133/50'),
     ('177/320', '89/160', '15/32', '19/40', '333873/200000', '5', '83/40', '11/4'),
     ('89/160', '357/640', '9/20', '29/64', '1693227/1000000', '3', '83/40', '11/4'),
     ('89/160', '357/640', '29/64', '73/160', '211439/125000', '3', '83/40', '11/4'),
     ('357/640', '179/320', '9/20', '29/64', '210947/125000', '3', '41/20', '133/50'),
     ('357/640', '179/320', '29/64', '73/160', '337177/200000', '3', '41/20', '133/50'),
     ('89/160', '357/640', '73/160', '147/320', '844833/500000', '3', '41/20', '133/50'),
     ('89/160', '357/640', '147/320', '37/80', '1687689/1000000', '3', '41/20', '133/50'),
     ('357/640', '179/320', '73/160', '147/320', '1684063/1000000', '3', '41/20', '67/25'),
     ('357/640', '179/320', '147/320', '37/80', '168211/100000', '3', '41/20', '27/10'),
     ('179/320', '9/16', '9/20', '73/160', '840939/500000', '3', '41/20', '137/50'),
     ('179/320', '359/640', '73/160', '147/320', '1678411/1000000', '3', '41/20', '27/10'),
     ('179/320', '359/640', '147/320', '37/80', '1676481/1000000', '3', '41/20', '68/25'),
     ('359/640', '9/16', '73/160', '147/320', '209089/125000', '3', '41/20', '68/25'),
     ('359/640', '9/16', '147/320', '37/80', '417701/250000', '3', '41/20', '137/50'),
     ('89/160', '357/640', '37/80', '149/320', '1684857/1000000', '5', '41/20', '67/25'),
     ('89/160', '357/640', '149/320', '15/32', '1675477/1000000', '5', '41/20', '133/50'),
     ('357/640', '179/320', '37/80', '149/320', '840013/500000', '3', '41/20', '27/10'),
     ('357/640', '179/320', '149/320', '15/32', '1673457/1000000', '5', '41/20', '27/10'),
     ('89/160', '179/320', '15/32', '19/40', '1665581/1000000', '5', '41/20', '68/25'),
     ('179/320', '359/640', '37/80', '149/320', '1674419/1000000', '3', '41/20', '68/25'),
     ('179/320', '359/640', '149/320', '15/32', '1671417/1000000', '5', '41/20', '137/50'),
     ('359/640', '9/16', '37/80', '149/320', '333753/200000', '3', '41/20', '137/50'),
     ('359/640', '9/16', '149/320', '15/32', '333319/200000', '3', '41/20', '69/25'),
     ('179/320', '9/16', '15/32', '19/40', '415429/250000', '5', '41/20', '139/50'),
     ('11/20', '177/320', '19/40', '77/160', '825453/500000', '5', '83/40', '267/100'),
     ('11/20', '177/320', '77/160', '39/80', '1626571/1000000', '5', '83/40', '263/100'),
     ('177/320', '89/160', '19/40', '77/160', '1647597/1000000', '5', '83/40', '273/100'),
     ('177/320', '89/160', '77/160', '39/80', '32473/20000', '5', '83/40', '269/100'),
     ('11/20', '177/320', '39/80', '79/160', '1599981/1000000', '5', '21/10', '269/100'),
     ('11/20', '177/320', '79/160', '1/2', '335671/200000', '3', '41/20', '68/25'),
     ('177/320', '89/160', '39/80', '79/160', '1597449/1000000', '5', '83/40', '267/100'),
     ('177/320', '89/160', '79/160', '1/2', '784459/500000', '5', '83/40', '263/100'),
     ('89/160', '179/320', '19/40', '77/160', '1644203/1000000', '5', '41/20', '67/25'),
     ('89/160', '179/320', '77/160', '39/80', '810323/500000', '5', '41/20', '133/50'),
     ('179/320', '9/16', '19/40', '77/160', '164073/100000', '5', '41/20', '69/25'),
     ('179/320', '9/16', '77/160', '39/80', '1617567/1000000', '5', '41/20', '68/25'),
     ('89/160', '9/16', '39/80', '1/2', '1594837/1000000', '5', '41/20', '137/50'),
     ('11/20', '177/320', '1/2', '81/160', '384933/250000', '5', '21/10', '261/100'),
     ('11/20', '177/320', '81/160', '41/80', '831673/500000', '3', '41/20', '69/25'),
     ('177/320', '89/160', '1/2', '81/160', '76899/50000', '5', '21/10', '267/100'),
     ('177/320', '89/160', '81/160', '41/80', '826597/500000', '3', '41/20', '14/5'),
     ('11/20', '177/320', '41/80', '83/160', '413783/250000', '3', '41/20', '69/25'),
     ('11/20', '177/320', '83/160', '21/40', '411613/250000', '3', '41/20', '139/50'),
     ('177/320', '89/160', '41/80', '83/160', '25704/15625', '3', '81/40', '68/25'),
     ('177/320', '89/160', '83/160', '21/40', '1636451/1000000', '3', '81/40', '68/25'),
     ('89/160', '179/320', '1/2', '81/160', '1536153/1000000', '5', '83/40', '53/20'),
     ('89/160', '179/320', '81/160', '41/80', '164281/100000', '3', '81/40', '137/50'),
     ('179/320', '9/16', '1/2', '81/160', '1534261/1000000', '5', '83/40', '271/100'),
     ('179/320', '9/16', '81/160', '41/80', '1632201/1000000', '3', '81/40', '14/5'),
     ('89/160', '179/320', '41/80', '83/160', '204343/125000', '3', '81/40', '69/25'),
     ('89/160', '179/320', '83/160', '21/40', '50819/31250', '3', '81/40', '69/25'),
     ('179/320', '9/16', '41/80', '83/160', '812101/500000', '3', '81/40', '14/5'),
     ('179/320', '9/16', '83/160', '21/40', '403933/250000', '3', '81/40', '141/50'),
     ('11/20', '89/160', '21/40', '43/80', '409329/250000', '3', '81/40', '139/50'),
     ('11/20', '89/160', '43/80', '11/20', '1617703/1000000', '3', '81/40', '139/50'),
     ('89/160', '9/16', '21/40', '43/80', '1617211/1000000', '3', '2', '277/100'),
     ('89/160', '9/16', '43/80', '11/20', '199733/125000', '3', '2', '277/100'),
     ('11/20', '9/16', '11/20', '9/16', '39909/25000', '3', '2', '283/100'),
     ('9/16', '23/40', '729/4096', '1/5', '1435961/1000000', '4', '12/5', '213/100'),
     ('9/16', '23/40', '1/5', '9/40', '294563/200000', '4', '23/10', '11/5'),
     ('9/16', '23/40', '9/40', '1/4', '1507379/1000000', '4', '23/10', '57/25'),
     ('9/16', '23/40', '1/4', '11/40', '767309/500000', '3', '9/4', '58/25'),
     ('9/16', '23/40', '11/40', '3/10', '1570033/1000000', '4', '11/5', '119/50'),
     ('9/16', '23/40', '3/10', '13/40', '99897/62500', '4', '43/20', '49/20'),
     ('9/16', '23/40', '13/40', '7/20', '812421/500000', '4', '17/8', '253/100'),
     ('9/16', '23/40', '7/20', '3/8', '1649659/1000000', '4', '21/10', '53/20'),
     ('9/16', '23/40', '3/8', '2/5', '1672983/1000000', '4', '41/20', '133/50'),
     ('9/16', '91/160', '2/5', '33/80', '1679217/1000000', '3', '83/40', '273/100'),
     ('9/16', '91/160', '33/80', '17/40', '67171/40000', '3', '41/20', '27/10'),
     ('91/160', '23/40', '2/5', '33/80', '1653779/1000000', '4', '41/20', '27/10'),
     ('91/160', '23/40', '33/80', '17/40', '206823/125000', '3', '81/40', '67/25'),
     ('9/16', '181/320', '17/40', '69/160', '419613/250000', '3', '41/20', '133/50'),
     ('9/16', '181/320', '69/160', '7/16', '1677241/1000000', '3', '41/20', '67/25'),
     ('181/320', '91/160', '17/40', '69/160', '83317/50000', '3', '41/20', '27/10'),
     ('181/320', '91/160', '69/160', '7/16', '104077/62500', '3', '41/20', '137/50'),
     ('9/16', '181/320', '7/16', '71/160', '837741/500000', '3', '41/20', '68/25'),
     ('9/16', '181/320', '71/160', '9/20', '83659/50000', '3', '41/20', '69/25'),
     ('181/320', '91/160', '7/16', '71/160', '831787/500000', '3', '41/20', '69/25'),
     ('181/320', '91/160', '71/160', '9/20', '1661369/1000000', '3', '81/40', '67/25'),
     ('91/160', '23/40', '17/40', '7/16', '827031/500000', '3', '81/40', '68/25'),
     ('91/160', '183/320', '7/16', '71/160', '330299/200000', '3', '81/40', '27/10'),
     ('91/160', '183/320', '71/160', '9/20', '329877/200000', '3', '81/40', '68/25'),
     ('183/320', '23/40', '7/16', '71/160', '819627/500000', '3', '81/40', '137/50'),
     ('183/320', '23/40', '71/160', '9/20', '409309/250000', '3', '81/40', '69/25'),
     ('9/16', '181/320', '9/20', '73/160', '83517/50000', '3', '41/20', '139/50'),
     ('9/16', '361/640', '73/160', '147/320', '833483/500000', '3', '41/20', '137/50'),
     ('9/16', '361/640', '147/320', '37/80', '41627/25000', '3', '41/20', '69/25'),
     ('361/640', '181/320', '73/160', '147/320', '830587/500000', '3', '41/20', '139/50'),
     ('361/640', '181/320', '147/320', '37/80', '165931/100000', '3', '41/20', '139/50'),
     ('181/320', '91/160', '9/20', '73/160', '1658621/1000000', '3', '81/40', '27/10'),
     ('181/320', '91/160', '73/160', '37/80', '206917/125000', '3', '81/40', '137/50'),
     ('9/16', '181/320', '37/80', '15/32', '831531/500000', '3', '81/40', '68/25'),
     ('9/16', '181/320', '15/32', '19/40', '1657777/1000000', '5', '81/40', '137/50'),
     ('181/320', '91/160', '37/80', '15/32', '1651519/1000000', '3', '81/40', '69/25'),
     ('181/320', '91/160', '15/32', '19/40', '1647173/1000000', '3', '81/40', '139/50'),
     ('91/160', '183/320', '9/20', '73/160', '205841/125000', '3', '81/40', '69/25'),
     ('91/160', '183/320', '73/160', '37/80', '164353/100000', '3', '81/40', '139/50'),
     ('183/320', '23/40', '9/20', '73/160', '1634667/1000000', '3', '81/40', '14/5'),
     ('183/320', '23/40', '73/160', '37/80', '815777/500000', '3', '81/40', '141/50'),
     ('91/160', '183/320', '37/80', '15/32', '327959/200000', '3', '81/40', '14/5'),
     ('91/160', '183/320', '15/32', '19/40', '163553/100000', '3', '81/40', '71/25'),
     ('183/320', '23/40', '37/80', '15/32', '16279/10000', '3', '2', '273/100'),
     ('183/320', '23/40', '15/32', '19/40', '50741/31250', '3', '2', '11/4'),
     ('9/16', '91/160', '19/40', '39/80', '818593/500000', '5', '81/40', '141/50'),
     ('9/16', '91/160', '39/80', '1/2', '397351/250000', '5', '81/40', '69/25'),
     ('91/160', '183/320', '19/40', '77/160', '10187/6250', '5', '2', '273/100'),
     ('91/160', '183/320', '77/160', '39/80', '803979/500000', '5', '81/40', '141/50'),
     ('183/320', '23/40', '19/40', '77/160', '809497/500000', '3', '2', '279/100'),
     ('183/320', '23/40', '77/160', '39/80', '80233/50000', '5', '2', '277/100'),
     ('91/160', '23/40', '39/80', '1/2', '395937/250000', '5', '2', '279/100'),
     ('9/16', '181/320', '1/2', '81/160', '1532311/1000000', '5', '41/20', '67/25'),
     ('9/16', '181/320', '81/160', '41/80', '810687/500000', '3', '81/40', '71/25'),
     ('181/320', '91/160', '1/2', '81/160', '1530311/1000000', '5', '41/20', '137/50'),
     ('181/320', '91/160', '81/160', '41/80', '50323/31250', '3', '2', '277/100'),
     ('9/16', '91/160', '41/80', '21/40', '1613439/1000000', '3', '2', '57/20'),
     ('91/160', '183/320', '1/2', '81/160', '95517/62500', '5', '81/40', '68/25'),
     ('91/160', '183/320', '81/160', '41/80', '1599097/1000000', '3', '2', '283/100'),
     ('183/320', '23/40', '1/2', '81/160', '763101/500000', '5', '81/40', '139/50'),
     ('183/320', '23/40', '81/160', '41/80', '1587663/1000000', '3', '2', '287/100'),
     ('91/160', '23/40', '41/80', '21/40', '397819/250000', '3', '79/40', '281/100'),
     ('9/16', '91/160', '21/40', '43/80', '199519/125000', '3', '2', '57/20'),
     ('9/16', '91/160', '43/80', '11/20', '157703/100000', '3', '2', '287/100'),
     ('91/160', '23/40', '21/40', '43/80', '7871/5000', '3', '79/40', '283/100'),
     ('91/160', '23/40', '43/80', '11/20', '1555263/1000000', '3', '79/40', '57/20'),
     ('9/16', '23/40', '11/20', '23/40', '778071/500000', '3', '39/20', '143/50'),
     ('23/40', '47/80', '12167/64000', '1/5', '1368497/1000000', '4', '23/10', '109/50'),
     ('23/40', '47/80', '1/5', '9/40', '87911/62500', '4', '23/10', '11/5'),
     ('23/40', '47/80', '9/40', '1/4', '72111/50000', '4', '9/4', '57/25'),
     ('23/40', '47/80', '1/4', '11/40', '367689/250000', '3', '11/5', '117/50'),
     ('23/40', '47/80', '11/40', '3/10', '1506607/1000000', '4', '11/5', '127/50'),
     ('23/40', '47/80', '3/10', '13/40', '1535583/1000000', '4', '43/20', '257/100'),
     ('23/40', '47/80', '13/40', '7/20', '781297/500000', '4', '21/10', '257/100'),
     ('23/40', '47/80', '7/20', '3/8', '793899/500000', '4', '83/40', '269/100'),
     ('23/40', '47/80', '3/8', '2/5', '805689/500000', '4', '81/40', '67/25'),
     ('23/40', '47/80', '2/5', '17/40', '814717/500000', '3', '2', '279/100'),
     ('23/40', '93/160', '17/40', '7/16', '407259/250000', '3', '81/40', '141/50'),
     ('23/40', '93/160', '7/16', '9/20', '813429/500000', '3', '2', '277/100'),
     ('93/160', '47/80', '17/40', '7/16', '1603433/1000000', '3', '2', '279/100'),
     ('93/160', '47/80', '7/16', '9/20', '160163/100000', '3', '2', '57/20'),
     ('23/40', '37/64', '9/20', '73/160', '101403/62500', '3', '2', '273/100'),
     ('23/40', '37/64', '73/160', '37/80', '202427/125000', '3', '2', '11/4'),
     ('37/64', '93/160', '9/20', '73/160', '402519/250000', '3', '2', '277/100'),
     ('37/64', '93/160', '73/160', '37/80', '12857/8000', '3', '2', '279/100'),
     ('23/40', '37/64', '37/80', '15/32', '1615841/1000000', '3', '2', '277/100'),
     ('23/40', '37/64', '15/32', '19/40', '1611727/1000000', '3', '2', '281/100'),
     ('37/64', '93/160', '37/80', '15/32', '801813/500000', '3', '2', '283/100'),
     ('37/64', '93/160', '15/32', '19/40', '49987/31250', '3', '2', '57/20'),
     ('93/160', '47/80', '9/20', '37/80', '1597561/1000000', '3', '79/40', '279/100'),
     ('93/160', '47/80', '37/80', '19/40', '1591263/1000000', '3', '79/40', '57/20'),
     ('23/40', '37/64', '19/40', '77/160', '1607079/1000000', '3', '2', '283/100'),
     ('23/40', '37/64', '77/160', '39/80', '160133/100000', '5', '2', '57/20'),
     ('37/64', '93/160', '19/40', '77/160', '398751/250000', '3', '2', '287/100'),
     ('37/64', '93/160', '77/160', '39/80', '397473/250000', '3', '79/40', '277/100'),
     ('23/40', '93/160', '39/80', '1/2', '1577941/1000000', '5', '79/40', '281/100'),
     ('93/160', '47/80', '19/40', '39/80', '197847/125000', '3', '79/40', '291/100'),
     ('93/160', '47/80', '39/80', '1/2', '98259/62500', '3', '39/20', '141/50'),
     ('23/40', '93/160', '1/2', '41/80', '1583269/1000000', '3', '79/40', '289/100'),
     ('23/40', '93/160', '41/80', '21/40', '1568321/1000000', '3', '79/40', '291/100'),
     ('93/160', '47/80', '1/2', '41/80', '194927/125000', '3', '39/20', '143/50'),
     ('93/160', '47/80', '41/80', '21/40', '1544643/1000000', '3', '39/20', '72/25'),
     ('23/40', '93/160', '21/40', '43/80', '77571/50000', '3', '79/40', '293/100'),
     ('23/40', '93/160', '43/80', '11/20', '1532631/1000000', '3', '39/20', '71/25'),
     ('93/160', '47/80', '21/40', '43/80', '763943/500000', '3', '39/20', '73/25'),
     ('93/160', '47/80', '43/80', '11/20', '1509207/1000000', '3', '39/20', '73/25'),
     ('23/40', '47/80', '11/20', '23/40', '1512023/1000000', '3', '77/40', '73/25'),
     ('23/40', '47/80', '23/40', '47/80', '18321/12500', '3', '39/20', '149/50'),
     ('47/80', '3/5', '103823/512000', '9/40', '669131/500000', '4', '9/4', '113/50'),
     ('47/80', '3/5', '9/40', '1/4', '85933/62500', '4', '9/4', '121/50'),
     ('47/80', '3/5', '1/4', '11/40', '702351/500000', '3', '11/5', '61/25'),
     ('47/80', '3/5', '11/40', '3/10', '180111/125000', '4', '43/20', '247/100'),
     ('47/80', '3/5', '3/10', '13/40', '294083/200000', '4', '21/10', '251/100'),
     ('47/80', '3/5', '13/40', '7/20', '1497823/1000000', '4', '83/40', '261/100'),
     ('47/80', '3/5', '7/20', '3/8', '152327/100000', '4', '41/20', '68/25'),
     ('47/80', '3/5', '3/8', '2/5', '1546939/1000000', '4', '2', '271/100'),
     ('47/80', '3/5', '2/5', '17/40', '1569041/1000000', '4', '79/40', '279/100'),
     ('47/80', '19/32', '17/40', '7/16', '1577313/1000000', '3', '79/40', '277/100'),
     ('47/80', '19/32', '7/16', '9/20', '787937/500000', '3', '79/40', '283/100'),
     ('19/32', '3/5', '17/40', '7/16', '1546257/1000000', '4', '79/40', '283/100'),
     ('19/32', '3/5', '7/16', '9/20', '1549653/1000000', '3', '39/20', '14/5'),
     ('47/80', '19/32', '9/20', '37/80', '393033/250000', '3', '79/40', '289/100'),
     ('47/80', '19/32', '37/80', '19/40', '783063/500000', '3', '39/20', '141/50'),
     ('19/32', '3/5', '9/20', '37/80', '1546227/1000000', '3', '39/20', '143/50'),
     ('19/32', '3/5', '37/80', '19/40', '1540499/1000000', '3', '39/20', '73/25'),
     ('47/80', '19/32', '19/40', '39/80', '311579/200000', '3', '39/20', '143/50'),
     ('47/80', '19/32', '39/80', '1/2', '386871/250000', '3', '39/20', '29/10'),
     ('19/32', '3/5', '19/40', '39/80', '1532507/1000000', '3', '39/20', '74/25'),
     ('19/32', '3/5', '39/80', '1/2', '1522297/1000000', '3', '77/40', '72/25'),
     ('47/80', '19/32', '1/2', '41/80', '76747/50000', '3', '39/20', '74/25'),
     ('47/80', '19/32', '41/80', '21/40', '380079/250000', '3', '39/20', '149/50'),
     ('19/32', '3/5', '1/2', '41/80', '377479/250000', '3', '77/40', '73/25'),
     ('19/32', '3/5', '41/80', '21/40', '1495417/1000000', '3', '77/40', '147/50'),
     ('47/80', '3/5', '21/40', '11/20', '1503671/1000000', '3', '19/10', '297/100'),
     ('47/80', '3/5', '11/20', '23/40', '1464581/1000000', '3', '19/10', '297/100'),
     ('47/80', '3/5', '23/40', '3/5', '44321/31250', '3', '19/10', '299/100'),
     ('3/5', '49/80', '27/125', '9/40', '1268203/1000000', '4', '9/4', '117/50'),
     ('3/5', '49/80', '9/40', '1/4', '652923/500000', '4', '11/5', '119/50'),
     ('3/5', '49/80', '1/4', '11/40', '83551/62500', '3', '43/20', '241/100'),
     ('3/5', '49/80', '11/40', '3/10', '1373247/1000000', '4', '17/8', '253/100'),
     ('3/5', '49/80', '3/10', '13/40', '701619/500000', '4', '83/40', '51/20'),
     ('3/5', '49/80', '13/40', '7/20', '1430937/1000000', '4', '41/20', '66/25'),
     ('3/5', '49/80', '7/20', '3/8', '1456501/1000000', '4', '81/40', '137/50'),
     ('3/5', '49/80', '3/8', '2/5', '1480113/1000000', '4', '79/40', '273/100'),
     ('3/5', '49/80', '2/5', '17/40', '75099/50000', '4', '39/20', '14/5'),
     ('3/5', '49/80', '17/40', '9/20', '761173/500000', '4', '77/40', '72/25'),
     ('3/5', '49/80', '9/20', '19/40', '1519913/1000000', '3', '19/10', '291/100'),
     ('3/5', '97/160', '19/40', '39/80', '376671/250000', '3', '77/40', '73/25'),
     ('3/5', '97/160', '39/80', '1/2', '1496659/1000000', '3', '77/40', '74/25'),
     ('97/160', '49/80', '19/40', '39/80', '740249/500000', '3', '19/10', '291/100'),
     ('97/160', '49/80', '39/80', '1/2', '1470643/1000000', '3', '19/10', '293/100'),
     ('3/5', '49/80', '1/2', '21/40', '742211/500000', '3', '15/8', '74/25'),
     ('3/5', '49/80', '21/40', '11/20', '58141/40000', '3', '15/8', '3'),
     ('3/5', '49/80', '11/20', '23/40', '1414477/1000000', '3', '15/8', '151/50'),
     ('3/5', '49/80', '23/40', '3/5', '21373/15625', '3', '15/8', '76/25'),
     ('3/5', '49/80', '3/5', '49/80', '82153/62500', '3', '15/8', '149/50'),
     ('49/80', '5/8', '117649/512000', '1/4', '1235317/1000000', '4', '43/20', '239/100'),
     ('49/80', '5/8', '1/4', '11/40', '19804/15625', '3', '17/8', '247/100'),
     ('49/80', '5/8', '11/40', '3/10', '1304063/1000000', '4', '83/40', '251/100'),
     ('49/80', '5/8', '3/10', '13/40', '83403/62500', '4', '41/20', '129/50'),
     ('49/80', '5/8', '13/40', '7/20', '85147/62500', '4', '81/40', '67/25'),
     ('49/80', '5/8', '7/20', '3/8', '1387931/1000000', '4', '2', '279/100'),
     ('49/80', '5/8', '3/8', '2/5', '705681/500000', '4', '79/40', '287/100'),
     ('49/80', '5/8', '2/5', '17/40', '28657/20000', '4', '77/40', '71/25'),
     ('49/80', '5/8', '17/40', '9/20', '1452633/1000000', '4', '19/10', '289/100'),
     ('49/80', '5/8', '9/20', '19/40', '183291/125000', '3', '15/8', '74/25'),
     ('49/80', '5/8', '19/40', '1/2', '727011/500000', '3', '15/8', '76/25'),
     ('49/80', '5/8', '1/2', '21/40', '1432331/1000000', '3', '37/20', '301/100'),
     ('49/80', '5/8', '21/40', '11/20', '700821/500000', '3', '37/20', '61/20'),
     ('49/80', '5/8', '11/20', '23/40', '54497/40000', '3', '37/20', '307/100'),
     ('49/80', '5/8', '23/40', '3/5', '1315253/1000000', '3', '37/20', '309/100'),
     ('49/80', '5/8', '3/5', '5/8', '630419/500000', '3', '37/20', '309/100'),
     ('5/8', '51/80', '125/512', '1/4', '1163679/1000000', '4', '17/8', '243/100'),
     ('5/8', '51/80', '1/4', '11/40', '598489/500000', '3', '21/10', '51/20'),
     ('5/8', '51/80', '11/40', '3/10', '308427/250000', '4', '41/20', '127/50'),
     ('5/8', '51/80', '3/10', '13/40', '1264437/1000000', '4', '81/40', '66/25'),
     ('5/8', '51/80', '13/40', '7/20', '1292483/1000000', '4', '2', '273/100'),
     ('5/8', '51/80', '7/20', '3/8', '329499/250000', '4', '79/40', '283/100'),
     ('5/8', '51/80', '3/8', '2/5', '26823/20000', '4', '39/20', '29/10'),
     ('5/8', '51/80', '2/5', '17/40', '1362143/1000000', '4', '19/10', '287/100'),
     ('5/8', '51/80', '17/40', '9/20', '345301/250000', '4', '15/8', '73/25'),
     ('5/8', '51/80', '9/20', '19/40', '1398601/1000000', '4', '15/8', '77/25'),
     ('5/8', '51/80', '19/40', '1/2', '280099/200000', '3', '37/20', '309/100'),
     ('5/8', '51/80', '1/2', '21/40', '43103/31250', '3', '73/40', '153/50'),
     ('5/8', '51/80', '21/40', '11/20', '1348701/1000000', '3', '73/40', '77/25'),
     ('5/8', '51/80', '11/20', '23/40', '32729/25000', '3', '73/40', '78/25'),
     ('5/8', '51/80', '23/40', '3/5', '630609/500000', '3', '73/40', '157/50'),
     ('5/8', '51/80', '3/5', '5/8', '1205551/1000000', '3', '73/40', '78/25'),
     ('5/8', '51/80', '5/8', '51/80', '35719/31250', '3', '73/40', '153/50'),
     ('51/80', '13/20', '132651/512000', '11/40', '562863/500000', '3', '41/20', '63/25'),
     ('51/80', '13/20', '11/40', '3/10', '581273/500000', '4', '81/40', '131/50'),
     ('51/80', '13/20', '3/10', '13/40', '1193589/1000000', '4', '2', '271/100'),
     ('51/80', '13/20', '13/40', '7/20', '610867/500000', '4', '79/40', '279/100'),
     ('51/80', '13/20', '7/20', '3/8', '623563/500000', '4', '39/20', '143/50'),
     ('51/80', '13/20', '3/8', '2/5', '1269931/1000000', '4', '19/10', '283/100'),
     ('51/80', '13/20', '2/5', '17/40', '1290341/1000000', '4', '19/10', '299/100'),
     ('51/80', '13/20', '17/40', '9/20', '40893/31250', '4', '15/8', '76/25'),
     ('51/80', '13/20', '9/20', '19/40', '1324891/1000000', '4', '37/20', '307/100'),
     ('51/80', '13/20', '19/40', '1/2', '20931/15625', '4', '73/40', '78/25'),
     ('51/80', '13/20', '1/2', '21/40', '662971/500000', '3', '9/5', '311/100'),
     ('51/80', '13/20', '21/40', '11/20', '647689/500000', '3', '9/5', '313/100'),
     ('51/80', '13/20', '11/20', '23/40', '1255417/1000000', '3', '9/5', '317/100'),
     ('51/80', '13/20', '23/40', '3/5', '1206571/1000000', '3', '9/5', '319/100'),
     ('51/80', '13/20', '3/5', '5/8', '1149473/1000000', '3', '9/5', '317/100'),
     ('51/80', '13/20', '5/8', '13/20', '1084911/1000000', '3', '9/5', '317/100'),
     ('13/20', '53/80', '2197/8000', '11/40', '105403/100000', '3', '81/40', '131/50'),
     ('13/20', '53/80', '11/40', '3/10', '1090923/1000000', '4', '2', '271/100'),
     ('13/20', '53/80', '3/10', '13/40', '1122271/1000000', '4', '39/20', '27/10'),
     ('13/20', '53/80', '13/40', '7/20', '575247/500000', '4', '77/40', '69/25'),
     ('13/20', '53/80', '7/20', '3/8', '293933/250000', '4', '19/10', '281/100'),
     ('13/20', '53/80', '3/8', '2/5', '18721/15625', '4', '15/8', '72/25'),
     ('13/20', '53/80', '2/5', '17/40', '1217913/1000000', '4', '15/8', '151/50'),
     ('13/20', '53/80', '17/40', '9/20', '1235247/1000000', '4', '37/20', '307/100'),
     ('13/20', '53/80', '9/20', '19/40', '1250389/1000000', '4', '73/40', '31/10'),
     ('13/20', '53/80', '19/40', '1/2', '1263621/1000000', '4', '9/5', '311/100'),
     ('13/20', '53/80', '1/2', '21/40', '1272871/1000000', '3', '71/40', '79/25'),
     ('13/20', '53/80', '21/40', '11/20', '621163/500000', '3', '71/40', '159/50'),
     ('13/20', '53/80', '11/20', '23/40', '600953/500000', '3', '71/40', '161/50'),
     ('13/20', '53/80', '23/40', '3/5', '1152089/1000000', '3', '71/40', '81/25'),
     ('13/20', '53/80', '3/5', '5/8', '54673/50000', '3', '71/40', '81/25'),
     ('13/20', '53/80', '5/8', '13/20', '205349/200000', '3', '71/40', '161/50'),
     ('13/20', '53/80', '13/20', '53/80', '476431/500000', '3', '71/40', '157/50'),
     ('53/80', '27/40', '148877/512000', '3/10', '31849/31250', '4', '39/20', '67/25'),
     ('53/80', '27/40', '3/10', '13/40', '1050829/1000000', '4', '77/40', '137/50'),
     ('53/80', '27/40', '13/40', '7/20', '107913/100000', '4', '19/10', '279/100'),
     ('53/80', '27/40', '7/20', '3/8', '276051/250000', '4', '15/8', '143/50'),
     ('53/80', '27/40', '3/8', '2/5', '1126203/1000000', '4', '37/20', '291/100'),
     ('53/80', '27/40', '2/5', '17/40', '1145299/1000000', '4', '37/20', '307/100'),
     ('53/80', '27/40', '17/40', '9/20', '1161689/1000000', '4', '73/40', '31/10'),
     ('53/80', '27/40', '9/20', '19/40', '587801/500000', '4', '9/5', '311/100'),
     ('53/80', '27/40', '19/40', '1/2', '593651/500000', '4', '71/40', '157/50'),
     ('53/80', '27/40', '1/2', '21/40', '1197103/1000000', '4', '71/40', '82/25'),
     ('53/80', '27/40', '21/40', '11/20', '595083/500000', '3', '7/4', '13/4'),
     ('53/80', '27/40', '11/20', '23/40', '574651/500000', '3', '7/4', '329/100'),
     ('53/80', '27/40', '23/40', '3/5', '274627/250000', '3', '7/4', '329/100'),
     ('53/80', '27/40', '3/5', '5/8', '1038321/1000000', '3', '7/4', '329/100'),
     ('53/80', '27/40', '5/8', '13/20', '484701/500000', '3', '7/4', '327/100'),
     ('53/80', '27/40', '13/20', '27/40', '892581/1000000', '3', '7/4', '13/4'),
     ('27/40', '11/16', '19683/64000', '13/40', '244897/250000', '4', '19/10', '283/100'),
     ('27/40', '11/16', '13/40', '7/20', '503993/500000', '4', '15/8', '72/25'),
     ('27/40', '11/16', '7/20', '3/8', '1032907/1000000', '4', '37/20', '291/100'),
     ('27/40', '11/16', '3/8', '2/5', '210899/200000', '4', '73/40', '74/25'),
     ('27/40', '11/16', '2/5', '17/40', '1072911/1000000', '4', '9/5', '301/100'),
     ('27/40', '11/16', '17/40', '9/20', '544171/500000', '4', '9/5', '63/20'),
     ('27/40', '11/16', '9/20', '19/40', '1101001/1000000', '4', '71/40', '157/50'),
     ('27/40', '11/16', '19/40', '1/2', '555567/500000', '4', '7/4', '317/100'),
     ('27/40', '11/16', '1/2', '21/40', '139879/125000', '4', '7/4', '329/100'),
     ('27/40', '11/16', '21/40', '11/20', '225007/200000', '4', '69/40', '82/25'),
     ('27/40', '11/16', '11/20', '23/40', '1098231/1000000', '3', '69/40', '84/25'),
     ('27/40', '11/16', '23/40', '3/5', '104651/100000', '3', '69/40', '84/25'),
     ('27/40', '11/16', '3/5', '5/8', '984803/1000000', '3', '69/40', '84/25'),
     ('27/40', '11/16', '5/8', '13/20', '913707/1000000', '3', '69/40', '167/50'),
     ('27/40', '11/16', '13/20', '27/40', '416983/500000', '3', '69/40', '83/25'),
     ('27/40', '11/16', '27/40', '11/16', '746519/1000000', '3', '69/40', '81/25'),
     ('11/16', '7/10', '1331/4096', '13/40', '908847/1000000', '4', '37/20', '57/20'),
     ('11/16', '7/10', '13/40', '7/20', '937379/1000000', '4', '73/40', '29/10'),
     ('11/16', '7/10', '7/20', '3/8', '481089/500000', '4', '73/40', '151/50'),
     ('11/16', '7/10', '3/8', '2/5', '491689/500000', '4', '9/5', '303/100'),
     ('11/16', '7/10', '2/5', '17/40', '250283/250000', '4', '71/40', '153/50'),
     ('11/16', '7/10', '17/40', '9/20', '1015613/1000000', '4', '7/4', '311/100'),
     ('11/16', '7/10', '9/20', '19/40', '51351/50000', '4', '7/4', '319/100'),
     ('11/16', '7/10', '19/40', '1/2', '1035583/1000000', '4', '69/40', '161/50'),
     ('11/16', '7/10', '1/2', '21/40', '32549/31250', '4', '69/40', '83/25'),
     ('11/16', '7/10', '21/40', '11/20', '130661/125000', '4', '17/10', '33/10'),
     ('11/16', '7/10', '11/20', '23/40', '209423/200000', '4', '17/10', '171/50'),
     ('11/16', '7/10', '23/40', '3/5', '12459/12500', '3', '17/10', '86/25'),
     ('11/16', '7/10', '3/5', '5/8', '186717/200000', '3', '17/10', '86/25'),
     ('11/16', '7/10', '5/8', '13/20', '860403/1000000', '3', '67/40', '331/100'),
     ('11/16', '7/10', '13/20', '27/40', '194459/250000', '3', '67/40', '329/100'),
     ('11/16', '7/10', '27/40', '7/10', '85839/125000', '3', '17/10', '84/25'),
     ('7/10', '57/80', '343/1000', '7/20', '867601/1000000', '4', '9/5', '297/100'),
     ('7/10', '57/80', '7/20', '3/8', '223081/250000', '4', '71/40', '151/50'),
     ('7/10', '57/80', '3/8', '2/5', '913179/1000000', '4', '71/40', '157/50'),
     ('7/10', '57/80', '2/5', '17/40', '232577/250000', '4', '7/4', '313/100'),
     ('7/10', '57/80', '17/40', '9/20', '14748/15625', '4', '69/40', '79/25'),
     ('7/10', '57/80', '9/20', '19/40', '119257/125000', '4', '69/40', '163/50'),
     ('7/10', '57/80', '19/40', '1/2', '961071/1000000', '4', '17/10', '163/50'),
     ('7/10', '57/80', '1/2', '21/40', '482581/500000', '4', '17/10', '169/50'),
     ('7/10', '57/80', '21/40', '11/20', '966617/1000000', '4', '67/40', '67/20'),
     ('7/10', '57/80', '11/20', '23/40', '966659/1000000', '4', '67/40', '69/20'),
     ('7/10', '57/80', '23/40', '3/5', '118713/125000', '3', '33/20', '341/100'),
     ('7/10', '57/80', '3/5', '5/8', '885281/1000000', '3', '33/20', '341/100'),
     ('7/10', '57/80', '5/8', '13/20', '405077/500000', '3', '33/20', '339/100'),
     ('7/10', '57/80', '13/20', '27/40', '724913/1000000', '3', '33/20', '67/20'),
     ('7/10', '57/80', '27/40', '7/10', '315143/500000', '3', '33/20', '333/100'),
     ('7/10', '57/80', '7/10', '57/80', '544191/1000000', '1', '33/20', '329/100'),
     ('57/80', '29/40', '185193/512000', '3/8', '205907/250000', '4', '7/4', '309/100'),
     ('57/80', '29/40', '3/8', '2/5', '844197/1000000', '4', '69/40', '157/50'),
     ('57/80', '29/40', '2/5', '17/40', '215189/250000', '4', '69/40', '81/25'),
     ('57/80', '29/40', '17/40', '9/20', '174691/200000', '4', '17/10', '161/50'),
     ('57/80', '29/40', '9/20', '19/40', '27577/31250', '4', '17/10', '84/25'),
     ('57/80', '29/40', '19/40', '1/2', '443989/500000', '4', '67/40', '331/100'),
     ('57/80', '29/40', '1/2', '21/40', '445111/500000', '4', '67/40', '343/100'),
     ('57/80', '29/40', '21/40', '11/20', '55647/62500', '4', '33/20', '339/100'),
     ('57/80', '29/40', '11/20', '23/40', '444729/500000', '4', '33/20', '351/100'),
     ('57/80', '29/40', '23/40', '3/5', '885991/1000000', '4', '13/8', '347/100'),
     ('57/80', '29/40', '3/5', '5/8', '840433/1000000', '3', '13/8', '347/100'),
     ('57/80', '29/40', '5/8', '13/20', '763547/1000000', '3', '13/8', '69/20'),
     ('57/80', '29/40', '13/20', '27/40', '675833/1000000', '3', '13/8', '343/100'),
     ('57/80', '29/40', '27/40', '7/10', '72241/125000', '3', '13/8', '339/100'),
     ('57/80', '29/40', '7/10', '29/40', '487041/1000000', '1', '13/8', '337/100'),
     ('29/40', '59/80', '24389/64000', '2/5', '776699/1000000', '4', '17/10', '16/5'),
     ('29/40', '59/80', '2/5', '17/40', '792759/1000000', '4', '67/40', '13/4'),
     ('29/40', '59/80', '17/40', '9/20', '804661/1000000', '4', '67/40', '331/100'),
     ('29/40', '59/80', '9/20', '19/40', '812563/1000000', '4', '33/20', '333/100'),
     ('29/40', '59/80', '19/40', '1/2', '816643/1000000', '4', '33/20', '339/100'),
     ('29/40', '59/80', '1/2', '21/40', '102177/125000', '4', '13/8', '341/100'),
     ('29/40', '59/80', '21/40', '11/20', '204277/250000', '4', '13/8', '69/20'),
     ('29/40', '59/80', '11/20', '23/40', '162839/200000', '4', '13/8', '357/100'),
     ('29/40', '59/80', '23/40', '3/5', '40409/50000', '4', '8/5', '353/100'),
     ('29/40', '59/80', '3/5', '5/8', '79939/100000', '4', '8/5', '359/100'),
     ('29/40', '59/80', '5/8', '13/20', '721099/1000000', '3', '8/5', '357/100'),
     ('29/40', '59/80', '13/20', '27/40', '631147/1000000', '3', '8/5', '71/20'),
     ('29/40', '59/80', '27/40', '7/10', '132557/250000', '3', '8/5', '351/100'),
     ('29/40', '59/80', '7/10', '29/40', '434847/1000000', '1', '8/5', '349/100'),
     ('29/40', '59/80', '29/40', '59/80', '78561/250000', '1', '8/5', '339/100'),
     ('59/80', '3/4', '205379/512000', '17/40', '181643/250000', '4', '33/20', '333/100'),
     ('59/80', '3/4', '17/40', '9/20', '737761/1000000', '4', '13/8', '337/100'),
     ('59/80', '3/4', '9/20', '19/40', '744639/1000000', '4', '13/8', '341/100'),
     ('59/80', '3/4', '19/40', '1/2', '747369/1000000', '4', '13/8', '351/100'),
     ('59/80', '3/4', '1/2', '21/40', '747491/1000000', '4', '8/5', '349/100'),
     ('59/80', '3/4', '21/40', '11/20', '37307/50000', '4', '8/5', '353/100'),
     ('59/80', '3/4', '11/20', '23/40', '741167/1000000', '4', '63/40', '89/25'),
     ('59/80', '3/4', '23/40', '3/5', '7327/10000', '4', '63/40', '179/50'),
     ('59/80', '3/4', '3/5', '5/8', '721031/1000000', '4', '63/40', '91/25'),
     ('59/80', '3/4', '5/8', '13/20', '683261/1000000', '3', '63/40', '37/10'),
     ('59/80', '3/4', '13/20', '27/40', '73917/125000', '3', '63/40', '92/25'),
     ('59/80', '3/4', '27/40', '7/10', '97539/200000', '3', '63/40', '91/25'),
     ('59/80', '3/4', '7/10', '29/40', '388143/1000000', '1', '63/40', '18/5'),
     ('59/80', '3/4', '29/40', '37/50', '32877/125000', '1', '63/40', '88/25'),
     ('37/50', '3/4', '37/50', '3/4', '803753/1000000', '2', '61/40', '393/100'),
     ('3/4', '61/80', '27/64', '17/40', '331211/500000', '4', '8/5', '339/100'),
     ('3/4', '61/80', '17/40', '9/20', '336497/500000', '4', '8/5', '69/20'),
     ('3/4', '61/80', '9/20', '19/40', '21217/31250', '4', '8/5', '351/100'),
     ('3/4', '61/80', '19/40', '1/2', '680537/1000000', '4', '63/40', '88/25'),
     ('3/4', '61/80', '1/2', '21/40', '340211/500000', '4', '63/40', '89/25'),
     ('3/4', '61/80', '21/40', '11/20', '677599/1000000', '4', '63/40', '183/50'),
     ('3/4', '61/80', '11/20', '23/40', '670671/1000000', '4', '31/20', '363/100'),
     ('3/4', '61/80', '23/40', '3/5', '82483/125000', '4', '31/20', '73/20'),
     ('3/4', '61/80', '3/5', '5/8', '645439/1000000', '4', '31/20', '373/100'),
     ('3/4', '61/80', '5/8', '13/20', '78463/125000', '4', '61/40', '371/100'),
     ('3/4', '61/80', '13/20', '27/40', '556813/1000000', '3', '61/40', '369/100'),
     ('3/4', '61/80', '27/40', '7/10', '450763/1000000', '3', '61/40', '73/20'),
     ('3/4', '61/80', '7/10', '29/40', '347381/1000000', '1', '61/40', '361/100'),
     ('3/4', '61/80', '29/40', '37/50', '218139/1000000', '1', '61/40', '71/20'),
     ('3/4', '61/80', '37/50', '3/4', '731911/1000000', '2', '3/2', '399/100'),
     ('3/4', '61/80', '3/4', '61/80', '705497/1000000', '2', '3/2', '399/100'),
     ('61/80', '31/40', '226981/512000', '9/20', '610573/1000000', '4', '63/40', '89/25'),
     ('61/80', '31/40', '9/20', '19/40', '307851/500000', '4', '31/20', '357/100'),
     ('61/80', '31/40', '19/40', '1/2', '308289/500000', '4', '31/20', '361/100'),
     ('61/80', '31/40', '1/2', '21/40', '154009/250000', '4', '31/20', '369/100'),
     ('61/80', '31/40', '21/40', '11/20', '152933/250000', '4', '61/40', '367/100'),
     ('61/80', '31/40', '11/20', '23/40', '301483/500000', '4', '61/40', '371/100'),
     ('61/80', '31/40', '23/40', '3/5', '589943/1000000', '4', '61/40', '15/4'),
     ('61/80', '31/40', '3/5', '5/8', '286449/500000', '4', '3/2', '15/4'),
     ('61/80', '31/40', '5/8', '13/20', '69013/125000', '4', '3/2', '377/100'),
     ('61/80', '31/40', '13/20', '27/40', '263969/500000', '3', '3/2', '379/100'),
     ('61/80', '31/40', '27/40', '7/10', '104951/250000', '3', '3/2', '15/4'),
     ('61/80', '31/40', '7/10', '29/40', '19559/62500', '1', '3/2', '369/100'),
     ('61/80', '31/40', '29/40', '37/50', '180001/1000000', '1', '3/2', '363/100'),
     ('61/80', '31/40', '37/50', '3/4', '12941/20000', '2', '59/40', '101/25'),
     ('61/80', '31/40', '3/4', '31/40', '618633/1000000', '2', '59/40', '41/10'),
     ('31/40', '63/80', '29791/64000', '19/40', '55511/100000', '4', '61/40', '367/100'),
     ('31/40', '63/80', '19/40', '1/2', '138889/250000', '4', '61/40', '373/100'),
     ('31/40', '63/80', '1/2', '21/40', '277209/500000', '4', '3/2', '373/100'),
     ('31/40', '63/80', '21/40', '11/20', '274377/500000', '4', '3/2', '15/4'),
     ('31/40', '63/80', '11/20', '23/40', '269139/500000', '4', '3/2', '379/100'),
     ('31/40', '63/80', '23/40', '3/5', '261587/500000', '4', '59/40', '19/5'),
     ('31/40', '63/80', '3/5', '5/8', '125913/250000', '4', '59/40', '191/50'),
     ('31/40', '63/80', '5/8', '13/20', '239979/500000', '4', '59/40', '96/25'),
     ('31/40', '63/80', '13/20', '27/40', '11559/25000', '0', '59/40', '97/25'),
     ('31/40', '63/80', '27/40', '7/10', '395139/1000000', '3', '59/40', '39/10'),
     ('31/40', '63/80', '7/10', '29/40', '285157/1000000', '1', '59/40', '193/50'),
     ('31/40', '63/80', '29/40', '37/50', '2327/15625', '1', '59/40', '94/25'),
     ('31/40', '63/80', '37/50', '3/4', '567947/1000000', '2', '29/20', '41/10'),
     ('31/40', '63/80', '3/4', '31/40', '537743/1000000', '2', '29/20', '104/25'),
     ('31/40', '63/80', '31/40', '63/80', '90697/200000', '2', '29/20', '102/25'),
     ('63/80', '4/5', '250047/512000', '1/2', '497159/1000000', '4', '59/40', '189/50'),
     ('63/80', '4/5', '1/2', '21/40', '495751/1000000', '4', '59/40', '191/50'),
     ('63/80', '4/5', '21/40', '11/20', '61107/125000', '4', '59/40', '193/50'),
     ('63/80', '4/5', '11/20', '23/40', '119201/250000', '4', '29/20', '193/50'),
     ('63/80', '4/5', '23/40', '3/5', '5747/12500', '4', '29/20', '39/10'),
     ('63/80', '4/5', '3/5', '5/8', '218957/500000', '4', '29/20', '98/25'),
     ('63/80', '4/5', '5/8', '13/20', '411483/1000000', '4', '29/20', '197/50'),
     ('63/80', '4/5', '13/20', '27/40', '195109/500000', '0', '29/20', '201/50'),
     ('63/80', '4/5', '27/40', '7/10', '377043/1000000', '3', '57/40', '397/100'),
     ('63/80', '4/5', '7/10', '29/40', '2643/10000', '1', '57/40', '391/100'),
     ('63/80', '4/5', '29/40', '37/50', '125193/1000000', '1', '57/40', '77/20'),
     ('63/80', '4/5', '37/50', '3/4', '123711/250000', '2', '57/40', '421/100'),
     ('63/80', '4/5', '3/4', '31/40', '463061/1000000', '2', '7/5', '207/50'),
     ('63/80', '4/5', '31/40', '4/5', '93509/250000', '2', '7/5', '41/10'),
     ('4/5', '13/16', '64/125', '21/40', '218527/500000', '4', '57/40', '391/100'),
     ('4/5', '13/16', '21/40', '11/20', '108051/250000', '4', '57/40', '79/20'),
     ('4/5', '13/16', '11/20', '23/40', '104679/250000', '4', '57/40', '397/100'),
     ('4/5', '13/16', '23/40', '3/5', '399879/1000000', '4', '57/40', '401/100'),
     ('4/5', '13/16', '3/5', '5/8', '46983/125000', '4', '57/40', '403/100'),
     ('4/5', '13/16', '5/8', '13/20', '173433/500000', '4', '7/5', '201/50'),
     ('4/5', '13/16', '13/20', '27/40', '32211/100000', '0', '7/5', '101/25'),
     ('4/5', '13/16', '27/40', '7/10', '365757/1000000', '3', '7/5', '41/10'),
     ('4/5', '13/16', '7/10', '29/40', '25061/100000', '1', '7/5', '101/25'),
     ('4/5', '13/16', '29/40', '37/50', '109031/1000000', '1', '7/5', '99/25'),
     ('4/5', '13/16', '37/50', '3/4', '427939/1000000', '2', '11/8', '421/100'),
     ('4/5', '13/16', '3/4', '31/40', '197391/500000', '2', '11/8', '423/100'),
     ('4/5', '13/16', '31/40', '4/5', '60309/200000', '2', '11/8', '417/100'),
     ('4/5', '13/16', '4/5', '13/16', '48513/250000', '2', '11/8', '411/100'),
     ('13/16', '33/40', '2197/4096', '11/20', '186467/500000', '4', '11/8', '403/100'),
     ('13/16', '33/40', '11/20', '23/40', '91041/250000', '4', '11/8', '81/20'),
     ('13/16', '33/40', '23/40', '3/5', '68737/200000', '4', '11/8', '409/100'),
     ('13/16', '33/40', '3/5', '5/8', '15883/50000', '4', '11/8', '411/100'),
     ('13/16', '33/40', '5/8', '13/20', '57253/200000', '4', '11/8', '411/100'),
     ('13/16', '33/40', '13/20', '27/40', '64549/250000', '0', '11/8', '413/100'),
     ('13/16', '33/40', '27/40', '7/10', '182213/500000', '3', '11/8', '427/100'),
     ('13/16', '33/40', '7/10', '29/40', '30693/125000', '1', '11/8', '421/100'),
     ('13/16', '33/40', '29/40', '37/50', '25161/250000', '1', '11/8', '411/100'),
     ('13/16', '33/40', '37/50', '3/4', '1837/5000', '2', '27/20', '431/100'),
     ('13/16', '33/40', '3/4', '31/40', '66613/200000', '2', '27/20', '433/100'),
     ('13/16', '33/40', '31/40', '4/5', '59037/250000', '2', '27/20', '427/100'),
     ('13/16', '33/40', '4/5', '33/40', '24769/200000', '2', '27/20', '421/100'),
     ('33/40', '67/80', '35937/64000', '23/40', '9497/31250', '4', '27/20', '417/100'),
     ('33/40', '67/80', '23/40', '3/5', '291313/1000000', '4', '27/20', '419/100'),
     ('33/40', '67/80', '3/5', '5/8', '263439/1000000', '4', '27/20', '421/100'),
     ('33/40', '67/80', '5/8', '13/20', '114909/500000', '4', '27/20', '423/100'),
     ('33/40', '67/80', '13/20', '27/40', '198611/1000000', '0', '27/20', '17/4'),
     ('33/40', '67/80', '27/40', '7/10', '93683/250000', '3', '53/40', '22/5'),
     ('33/40', '67/80', '7/10', '29/40', '254511/1000000', '1', '53/40', '217/50'),
     ('33/40', '67/80', '29/40', '37/50', '26969/250000', '1', '53/40', '106/25'),
     ('33/40', '67/80', '37/50', '3/4', '313367/1000000', '2', '53/40', '221/50'),
     ('33/40', '67/80', '3/4', '31/40', '55609/200000', '2', '53/40', '111/25'),
     ('33/40', '67/80', '31/40', '4/5', '4449/25000', '2', '53/40', '219/50'),
     ('33/40', '67/80', '4/5', '33/40', '61421/1000000', '2', '53/40', '43/10'),
     ('33/40', '67/80', '33/40', '5/6', '-3551/50000', '2', '53/40', '211/50'),
     ('5/6', '67/80', '5/6', '67/80', '7943/31250', '6', '13/10', '112/25'),
     ('67/80', '17/20', '300763/512000', '3/5', '1431/6250', '4', '13/10', '107/25'),
     ('67/80', '17/20', '3/5', '5/8', '213321/1000000', '4', '13/10', '43/10'),
     ('67/80', '17/20', '5/8', '13/20', '44411/250000', '4', '13/10', '108/25'),
     ('67/80', '17/20', '13/20', '27/40', '71737/500000', '0', '13/10', '108/25'),
     ('67/80', '17/20', '27/40', '7/10', '392559/1000000', '3', '51/40', '227/50'),
     ('67/80', '17/20', '7/10', '29/40', '67837/250000', '1', '13/10', '113/25'),
     ('67/80', '17/20', '29/40', '37/50', '12379/100000', '1', '13/10', '22/5'),
     ('67/80', '17/20', '37/50', '3/4', '132981/500000', '2', '51/40', '113/25'),
     ('67/80', '17/20', '3/4', '31/40', '2873/12500', '2', '51/40', '113/25'),
     ('67/80', '17/20', '31/40', '4/5', '127079/1000000', '2', '13/10', '113/25'),
     ('67/80', '17/20', '4/5', '33/40', '1369/200000', '2', '13/10', '223/50'),
     ('67/80', '17/20', '33/40', '5/6', '-16299/125000', '2', '13/10', '217/50'),
     ('67/80', '17/20', '5/6', '17/20', '7943/31250', '6', '51/40', '233/50'),
     ('17/20', '69/80', '4913/8000', '5/8', '73487/500000', '4', '51/40', '22/5'),
     ('17/20', '69/80', '5/8', '13/20', '129847/1000000', '4', '51/40', '111/25'),
     ('17/20', '69/80', '13/20', '27/40', '92887/1000000', '0', '51/40', '111/25'),
     ('17/20', '69/80', '27/40', '7/10', '104511/250000', '3', '5/4', '473/100'),
     ('17/20', '69/80', '7/10', '29/40', '148093/500000', '1', '5/4', '467/100'),
     ('17/20', '69/80', '29/40', '37/50', '148079/1000000', '1', '5/4', '91/20'),
     ('17/20', '69/80', '37/50', '3/4', '225291/1000000', '2', '5/4', '463/100'),
     ('17/20', '69/80', '3/4', '31/40', '3771/20000', '2', '5/4', '93/20'),
     ('17/20', '69/80', '31/40', '4/5', '83589/1000000', '2', '5/4', '457/100'),
     ('17/20', '69/80', '4/5', '33/40', '-19911/500000', '2', '5/4', '451/100'),
     ('17/20', '69/80', '33/40', '5/6', '-90641/500000', '2', '5/4', '441/100'),
     ('17/20', '69/80', '5/6', '17/20', '7943/31250', '6', '5/4', '97/20'),
     ('17/20', '69/80', '17/20', '69/80', '52947/1000000', '6', '5/4', '93/20'),
     ('69/80', '7/8', '328509/512000', '13/20', '5669/100000', '4', '5/4', '91/20'),
     ('69/80', '7/8', '13/20', '27/40', '46939/1000000', '0', '49/40', '453/100'),
     ('69/80', '7/8', '27/40', '7/10', '451313/1000000', '3', '49/40', '99/20'),
     ('69/80', '7/8', '7/10', '29/40', '61671/200000', '2', '49/40', '97/20'),
     ('69/80', '7/8', '29/40', '37/50', '9043/50000', '1', '49/40', '19/4'),
     ('69/80', '7/8', '37/50', '3/4', '23931/125000', '2', '49/40', '477/100'),
     ('69/80', '7/8', '3/4', '31/40', '30853/200000', '2', '49/40', '477/100'),
     ('69/80', '7/8', '31/40', '4/5', '23783/500000', '2', '49/40', '471/100'),
     ('69/80', '7/8', '4/5', '33/40', '-39263/500000', '2', '49/40', '463/100'),
     ('69/80', '7/8', '33/40', '5/6', '-223669/1000000', '2', '49/40', '451/100'),
     ('69/80', '7/8', '5/6', '17/20', '7943/31250', '6', '6/5', '124/25'),
     ('69/80', '7/8', '17/20', '7/8', '52947/1000000', '6', '49/40', '97/20'),
     ('7/8', '71/80', '343/512', '27/40', '-1497/40000', '0', '6/5', '231/50'),
     ('7/8', '141/160', '27/40', '11/16', '235453/500000', '3', '6/5', '5'),
     ('7/8', '141/160', '11/16', '7/10', '408427/1000000', '3', '6/5', '124/25'),
     ('141/160', '71/80', '2803221/4096000', '11/16', '223119/500000', '3', '47/40', '101/20'),
     ('141/160', '71/80', '11/16', '7/10', '430261/1000000', '3', '47/40', '101/20'),
     ('7/8', '71/80', '7/10', '29/40', '70283/250000', '2', '47/40', '99/20'),
     ('7/8', '71/80', '29/40', '37/50', '214493/1000000', '2', '47/40', '491/100'),
     ('7/8', '71/80', '37/50', '3/4', '4113/25000', '2', '6/5', '123/25'),
     ('7/8', '71/80', '3/4', '31/40', '12707/100000', '2', '47/40', '489/100'),
     ('7/8', '71/80', '31/40', '4/5', '9541/500000', '2', '6/5', '243/50'),
     ('7/8', '71/80', '4/5', '33/40', '-3413/31250', '2', '6/5', '119/25'),
     ('7/8', '71/80', '33/40', '5/6', '-32191/125000', '2', '6/5', '116/25'),
     ('7/8', '71/80', '5/6', '17/20', '7943/31250', '6', '47/40', '103/20'),
     ('7/8', '71/80', '17/20', '7/8', '52947/1000000', '6', '47/40', '99/20'),
     ('7/8', '71/80', '7/8', '71/80', '-257613/1000000', '6', '6/5', '118/25'),
     ('71/80', '143/160', '357911/512000', '716311/1024000', '392659/1000000', '3', '47/40', '513/100'),
     ('71/80', '143/160', '716311/1024000', '7/10', '97507/250000', '3', '47/40', '513/100'),
     ('71/80', '9/10', '7/10', '29/40', '260241/1000000', '2', '23/20', '51/10'),
     ('71/80', '9/10', '29/40', '37/50', '194451/1000000', '2', '23/20', '253/50'),
     ('71/80', '9/10', '37/50', '3/4', '36147/250000', '2', '23/20', '251/50'),
     ('71/80', '9/10', '3/4', '31/40', '107041/1000000', '2', '23/20', '251/50'),
     ('71/80', '9/10', '31/40', '4/5', '-1797/1000000', '2', '23/20', '124/25'),
     ('71/80', '9/10', '4/5', '33/40', '-131841/1000000', '2', '23/20', '122/25'),
     ('71/80', '9/10', '33/40', '5/6', '-282831/1000000', '2', '47/40', '479/100'),
     ('71/80', '9/10', '5/6', '17/20', '7943/31250', '6', '23/20', '267/50'),
     ('71/80', '9/10', '17/20', '7/8', '52947/1000000', '6', '23/20', '257/50'),
     ('71/80', '9/10', '7/8', '9/10', '-257613/1000000', '6', '23/20', '243/50'),
     ('9/10', '73/80', '729/1000', '37/50', '8441/50000', '2', '9/8', '26/5'),
     ('9/10', '73/80', '37/50', '3/4', '131727/1000000', '2', '9/8', '259/50'),
     ('9/10', '73/80', '3/4', '31/40', '23563/250000', '2', '9/8', '259/50'),
     ('9/10', '73/80', '31/40', '4/5', '-15007/1000000', '2', '9/8', '128/25'),
     ('9/10', '73/80', '4/5', '33/40', '-36587/250000', '2', '9/8', '251/50'),
     ('9/10', '73/80', '33/40', '5/6', '-149773/500000', '2', '9/8', '49/10'),
     ('9/10', '73/80', '5/6', '17/20', '7943/31250', '6', '11/10', '273/50'),
     ('9/10', '73/80', '17/20', '7/8', '52947/1000000', '6', '9/8', '133/25'),
     ('9/10', '73/80', '7/8', '9/10', '-257613/1000000', '6', '9/8', '251/50'),
     ('9/10', '73/80', '9/10', '73/80', '-11589/20000', '6', '9/8', '119/25'),
     ('73/80', '37/40', '389017/512000', '31/40', '12717/250000', '2', '11/10', '133/25'),
     ('73/80', '37/40', '31/40', '4/5', '-4539/250000', '2', '11/10', '132/25'),
     ('73/80', '37/40', '4/5', '33/40', '-18849/125000', '2', '11/10', '259/50'),
     ('73/80', '37/40', '33/40', '5/6', '-307053/1000000', '2', '11/10', '126/25'),
     ('73/80', '37/40', '5/6', '17/20', '7943/31250', '6', '43/40', '563/100'),
     ('73/80', '37/40', '17/20', '7/8', '52947/1000000', '6', '11/10', '11/2'),
     ('73/80', '37/40', '7/8', '9/10', '-257613/1000000', '6', '11/10', '259/50'),
     ('73/80', '37/40', '9/10', '37/40', '-11589/20000', '6', '11/10', '123/25'),
     ('37/40', '15/16', '50653/64000', '4/5', '-46251/500000', '2', '43/40', '537/100'),
     ('37/40', '15/16', '4/5', '33/40', '-28123/200000', '2', '43/40', '537/100'),
     ('37/40', '15/16', '33/40', '5/6', '-148877/500000', '2', '43/40', '521/100'),
     ('37/40', '15/16', '5/6', '17/20', '-54991/1000000', '7', '43/40', '551/100'),
     ('37/40', '15/16', '17/20', '7/8', '-57299/250000', '7', '43/40', '107/20'),
     ('37/40', '15/16', '7/8', '9/10', '-248909/500000', '7', '43/40', '511/100'),
     ('37/40', '15/16', '9/10', '37/40', '-387951/500000', '7', '43/40', '499/100'),
     ('37/40', '15/16', '37/40', '15/16', '-133033/125000', '7', '43/40', '499/100'),
     ('15/16', '19/20', '3375/4096', '33/40', '-272723/1000000', '2', '21/20', '539/100'),
     ('15/16', '19/20', '33/40', '5/6', '-69921/250000', '2', '21/20', '541/100'),
     ('15/16', '19/20', '5/6', '17/20', '-54991/1000000', '7', '21/20', '569/100'),
     ('15/16', '19/20', '17/20', '7/8', '-57299/250000', '7', '21/20', '551/100'),
     ('15/16', '19/20', '7/8', '9/10', '-248909/500000', '7', '21/20', '527/100'),
     ('15/16', '19/20', '9/10', '37/40', '-387951/500000', '7', '21/20', '509/100'),
     ('15/16', '19/20', '37/40', '19/20', '-133033/125000', '7', '21/20', '511/100'),
     ('19/20', '77/80', '6859/8000', '7/8', '-153751/500000', '7', '41/40', '561/100'),
     ('19/20', '77/80', '7/8', '9/10', '-248909/500000', '7', '41/40', '543/100'),
     ('19/20', '77/80', '9/10', '37/40', '-387951/500000', '7', '41/40', '523/100'),
     ('19/20', '77/80', '37/40', '19/20', '-133033/125000', '7', '41/40', '523/100'),
     ('19/20', '77/80', '19/20', '77/80', '-21309/15625', '7', '41/40', '21/4'),
     ('77/80', '39/40', '456533/512000', '9/10', '-682099/1000000', '7', '1', '543/100'),
     ('77/80', '39/40', '9/10', '37/40', '-387951/500000', '7', '1', '537/100'),
     ('77/80', '39/40', '37/40', '19/20', '-133033/125000', '7', '1', '107/20'),
     ('77/80', '39/40', '19/20', '39/40', '-21309/15625', '7', '1', '537/100'),
     ('39/40', '79/80', '59319/64000', '19/20', '-217229/200000', '7', '39/40', '547/100'),
     ('39/40', '79/80', '19/20', '39/40', '-21309/15625', '7', '39/40', '549/100'),
     ('39/40', '79/80', '39/40', '79/80', '-837681/500000', '7', '39/40', '549/100'),
     ('79/80', '1', '493039/512000', '39/40', '-76191/50000', '7', '19/20', '281/50'),
     ('79/80', '1', '39/40', '1', '-837681/500000', '7', '19/20', '141/25'),
    ]
    witness={}
    for row in raw:
     vals=tuple(map(F,row));key=vals[:4]
     assert key not in witness
     witness[key]=vals[4:]
    count=0;lowest=F(1)
    def rec(kl,kh,al,ah,depth):
     nonlocal count,lowest
     kl=max(kl,al);al=max(al,kl**3);ah=min(ah,kh)
     if kl>=kh or al>=ah:return
     key=(kl,kh,al,ah)
     if key not in witness:
      assert depth<5,('uncovered rectangle',key)
      km=(kl+kh)/2;am=(al+ah)/2
      for ll,hh in[(kl,km),(km,kh)]:
       for aa,bb in[(al,am),(am,ah)]:rec(ll,hh,aa,bb,depth+1)
      return
     J,ii,q,c=witness.pop(key);i=int(ii);assert ii==i
     assert q in CV or (F(9,10)<=q<=2 and(q*40).denominator==1)
     assert c>0 and c<=8 and(c*100).denominator==1
     choices=[]
     if ah<=F(27,40):choices.append(0)
     if al>=F(1,4)and ah<=F(37,50):choices.append(1)
     if al>=F(7,10)and ah<=F(5,6):choices.append(2)
     if al>=F(1,4)and ah<=F(7,10):choices.append(3)
     if ah<=F(13,20):choices.append(4)
     if al>=F(1,4)and ah<=F(51,100)and kh<=F(13,20):choices.append(5)
     if al>=F(5,6):choices.append(6)
     if kl>=F(37,40):choices.append(7)
     assert i in choices
     if i<6:
      P=add(mul(add(scale(one,J),scale(Bs[i],-1),Hs[i]),D),scale(N,-1))
      na=max(a for a,r in P);nr=max(r for a,r in P)
      assert min(bc(D,al,ah,kl,kh,na,nr))>0
     else:P=add(scale(one,J),scale(Jnorm if i==6 else Jnormhigh,-1))
     assert min(bc(P,al,ah,kl,kh))>0
     mg=entropy(kh,ah,J,q,c)
     assert mg>F(1,100000)
     lowest=min(lowest,mg);count+=1
    ap=sorted(set([F(i,40)for i in range(41)]+[F(37,50),F(5,6),F(27,40)]))
    for ki in range(32,80):
     for al,ah in zip(ap,ap[1:]):rec(F(ki,80),F(ki+1,80),al,ah,0)
    assert not witness
    assert count==1330
    print('PASS: general gamma=47/20; 1330 joint rectangles, complete coverage and exact entropy margins.')


def check_uniform_lower_plateau() -> None:
    from fractions import Fraction as F
    from math import comb, factorial
    def add(*ps):
        out=[F(0)]*max(map(len,ps))
        for p in ps:
            for j,x in enumerate(p):out[j]+=x
        return out
    def scale(p,x):return [a*x for a in p]
    def mul(p,q):
        out=[F(0)]*(len(p)+len(q)-1)
        for i,a in enumerate(p):
            for j,b in enumerate(q):out[i+j]+=a*b
        return out
    def der(p):return [j*p[j]for j in range(1,len(p))]
    def val(p,x):return sum(c*x**j for j,c in enumerate(p))
    def bern(p,a,b):
        n=len(p)-1
        q=[sum(p[j]*comb(j,r)*a**(j-r)*(b-a)**r for j in range(r,n+1))for r in range(n+1)]
        return [sum(q[r]*F(comb(j,r),comb(n,r))for r in range(j+1))for j in range(n+1)]
    def exp_low(x,n=24):
        assert x>=0
        return sum((x**j/F(factorial(j)) for j in range(n+1)),F(0))
    u=F(1207,1000);w=F(26,25);c=F(17,10);s=F(347,500)
    c4=F(5);cap=F(4137,1000);left=F(71,100);right=F(147,200)
    a0=F(6,5);a1=F(1211,1000);v0=F(1631,1000);v1=F(167,100)
    for A,v,lower in [(a0,v0,63549),(a1,v1,64243)]:
        assert 1+2*A*right-3*c*right*right>0
        d=lambda x:1-u*(x+A*x*x-c*x**3)
        psi=lambda x:u*x+2*v*x*x-2*w*x**4
        assert d(right)>0
        p=[4*v-u*u-2*u*A,3*u*c-u*u*A-4*u*v,
           u*u*c-4*u*v*A-8*w,4*u*v*c+8*u*w,8*u*w*A,-8*u*w*c]
        trans=[sum(p[r]*right**r*comb(5-r,j-r)for r in range(j+1))for j in range(6)]
        assert [1 if x>0 else -1 for x in trans]==[1,1,1,-1,-1,1]
        lo,hi=F(lower,10**5),F(lower+1,10**5)
        assert p[0]>0 and val(p,lo)<0<val(p,hi)
        assert hi<left
        assert u+4*v*lo-8*w*hi**3>0
        assert d(hi)*exp_low(psi(lo))>1
    A=[F(7,10)*(1+s*s)/(2*s),F(1),-F(7,10)/(2*s)]
    assert min(bern(der(A),left,right))>0
    assert a0<=val(A,left)<val(A,right)<=a1
    assert right*right<F(100,149)
    v=add([v0],scale(add(A,[-a0]),(v1-v0)/(a1-a0)))
    E=add(mul(v,[1,0,-1]),[-4+w/2,-u/2,0,0,w])
    d=add([1,-u,0,u*c],scale([0,0]+A,-u))
    Q=add(scale(mul(d,der(E)),2),scale(der(d),-1))
    assert max(bern(der(Q),left,right))<-5
    assert max(bern(der(E),left,right))<0
    assert max(bern(der(d),left,right))<0
    lo,hi=F(72167,10**5),F(72168,10**5)
    assert val(Q,lo)>0>val(Q,hi)
    assert val(d,hi)>0 and val(E,lo)<0 and u*cap>4
    assert exp_low(-2*val(E,lo))>16*c4*c4/(9*w*w*(u*cap-4)**2*val(d,hi))
    # B2 branch for kappa >= 147/200, including its scalar certificate.
    a=right;A=F(74,55);u=F(6,5);v=F(27,16);w=F(21,20);c=F(19,10)
    dd=lambda x:1-u*(x+A*x*x-c*x**3)
    psi=lambda x:u*x+2*v*x*x-2*w*x**4
    p=[4*v-u*u-2*u*A,3*u*c-u*u*A-4*u*v,
       u*u*c-4*u*v*A-8*w,4*u*v*c+8*u*w,8*u*w*A,-8*u*w*c]
    trans=[sum(p[r]*comb(5-r,j-r)for r in range(j+1))for j in range(6)]
    assert [1 if x>0 else -1 for x in trans]==[1,1,-1,-1,1,1]
    lo,hi=F(607,1000),F(608,1000)
    assert p[0]>0 and val(p,lo)<0<val(p,hi)
    assert 1+2*A*lo-3*c*lo*lo>0 and 1+2*A*hi-3*c*hi*hi>0
    assert u+4*v*lo-8*w*hi**3>0
    assert dd(hi)*exp_low(psi(lo))>1
    assert A*A>1+(c-1)**2 and 1+A-c>0
    d=dd(a)
    E=v-4+w/2-u*a/2-v*a*a+w*a**4
    assert d>0 and E<0 and u*cap>4
    assert exp_low(-2*E)>16*c4*c4/(9*w*w*(u*cap-4)**2*d)

    print("PASS: simplified general lower plateau4137/1000 using fourth-moment coefficient5.")


def check_uniform_lower_higher_moments() -> None:
    from fractions import Fraction as F
    from math import factorial

    # All bounds and comparisons use exact rational arithmetic.
    ROUND=10**12
    def up(x): return F(-((-x.numerator*ROUND)//x.denominator),ROUND)
    def down(x): return F((x.numerator*ROUND)//x.denominator,ROUND)
    def hu(k):
     return min(F(4137,1000),max(F(3,2),F(57,40)+F(23,10)*k+F(47,20)*k*k-F(3,10)*k**3))
    def log_up(x,n=24):
     assert x>=1
     z=(x-1)/(x+1); z2=z*z
     t=z;s=F(0)
     for j in range(n):
      s+=2*t/(2*j+1);t*=z2
     return up(s+2*t/((2*n+1)*(1-z2)))
    def exp_lo(x,n=24):
     assert x>=0
     s=F(1);t=F(1)
     for j in range(1,n+1):
      t*=x/j;s+=t
     return s
    def exp_up(x,n=40):
     assert 0<=x<n+2
     s=exp_lo(x,n)
     return s+x**(n+1)/factorial(n+1)/(1-x/F(n+2))
    def jup(z):
     assert 0<=z<1
     return log_up(1/(1-z))-z
    def mc_low(z,n=60):
     assert 0<=z<1
     t=z*z;s=F(0)
     for j in range(2,n+1):
      s+=2*t/(j*(j+1));t*=z
     return s
    def log_m_minus_one_up(k,p):
     D=1+2*p*k*k-4*k**4
     ell=up(log_up(D)/(2*k*k))
     if ell>=8:return ell
     lower_e=down(1/exp_up(ell))
     return ell-sum(lower_e**j/F(j) for j in range(1,7))
    def entropy_other_up(k,p):
     B=2*k*k+1/(p-2*k*k)
     return p*log_up(B*p)+1/(exp_lo(p-F(1,20))-1)
    def certificate(lo,hi,p,small=False):
     uu=4*p/((p-1)*hu(lo));ul=4*p/((p-1)*hu(hi))
     assert uu*hi<1
     if small:
      assert uu==ul and ul*ul>=3
     else:
      assert mc_low(ul*lo)>=lo*lo
     gu=jup(uu*hi)/(2*hi*hi)
     rhs=(p-1)*gu+log_m_minus_one_up(lo,p)+entropy_other_up(hi,p)
     assert rhs<3*p
     return 3*p-rhs

    assert exp_lo(F(47,10))>95
    assert certificate(F(3,100),F(3,100),F(50),True)>F(1,100)
    count=0
    for j in range(30,711):
        mid=F(2*j+1,2*1000)
        if mid<F(13,20):
            p=F(37,10)+F(13,10)/mid-mid**2/2
        else:
            p=F(12)-10*mid
        assert p>=F(19,4)
        assert certificate(F(j,1000),F(j+1,1000),p)>F(1,10000),j
        count+=1
    assert count==681
    assert hu(F(3,100))==F(3,2)
    pi=lambda k:F(57,40)+F(23,10)*k+F(47,20)*k*k-F(3,10)*k**3
    assert pi(F(711,1000))>F(4137,1000)
    assert pi(F(1,30))>F(3,2) and pi(F(1,2))>3
    assert F(3,2)+3>F(4137,1000)
    s=F(713,1000);A=F(57,40);B=F(23,10);C=F(47,20);D=F(-3,10)
    angle=F(793769,10**6);r=F(701165,10**6);r0=F(999444,10**6)
    q=F(4137,1000)-A-2*C/3-C*s*s/3-B*s/2-D*s*(3+2*s*s)/8
    assert q>0 and r*r>1-s*s and r0*r0<1-F(1,30)**2
    assert sum((-1)**j*angle**(2*j+1)/F(factorial(2*j+1))for j in range(4))>s
    bound=A+2*C/3+F(83,80)*angle+q*r+F(3,40)*(1-r0)
    assert bound==F(92147397657384409,24000000000000000)<F(96,25)
    print("PASS: simplified general alpha96/25;681 moment cells and exact integral.")

def check_uniform_lower_beta():
    """Old cosh interpolation suffices for the rounded beta=79/50."""
    from fractions import Fraction as F
    from math import factorial
    def low(x):return sum(x**j/F(factorial(j))for j in range(25))
    def high(x):
        assert 0<=x<26
        return low(x)+x**25/F(factorial(25))/(1-x/F(26))
    c=F(499,100);a=c/2-2
    assert a==F(99,200)
    assert 20<low(F(3)) and high(F(3))<21
    assert low(F(751,250))>2*c/a
    assert low(F(259,80))>F(499,20)
    assert F(1,4)-1/(2*c)>F(7,50)
    assert -F(1,250)+F(7,50*21)>0
    assert a-F(2,5)>0
    assert c<2*F(79,50)**2
    print("PASS: simplified general beta79/50 from the offset fourth moment.")


def check_tail_moment_cutoff():
    """Certify the common q=9/10 cutoff used for higher moments."""
    exp_lower=sum(F(27,8)**j/factorial(j) for j in range(15))
    assert exp_lower>F(146,5)
    assert F(3163,1000)**2>10
    assert F(20,9)*F(3163,1000)/F(146,5)<F(1,4)
    nu=F(9,2)
    assert F(25225,1296)<nu**2 and F(10896875,186624)<nu**3
    assert F(295,72)<nu
    # The single q=9/10 tail suffices for the second moment at L>=5/4.
    def expl(x):return sum(x**j/factorial(j) for j in range(25))
    def expu(x):return expl(x)+x**25/factorial(25)/(1-x/26)
    f=F(15,4)+F(1,4)/expl(F(11,32))*(F(15,4)+F(16,9))-F(2,5)/expu(F(1,2))
    assert f<F(9,2)
    # Coefficients of the negative derivative bound in powers of L-1.
    assert F(165,128)-F(17,72)+F(1,18)>0
    assert F(330,128)-F(17,72)>0
    print('PASS: common tail cutoff, higher moments, and single-rate second moment for L>=5/4.')


def check_general_upper_second_moment():
    S=10**12
    def up(x):return F(-((-x.numerator*S)//x.denominator),S)
    def down(x):return F((x.numerator*S)//x.denominator,S)
    def expl(x):return sum(x**j/factorial(j) for j in range(49))
    def expu(x):return expl(x)+x**49/factorial(49)/(1-x/50)
    def eu(x):
        assert abs(x)<50
        return up(expu(x) if x>=0 else 1/expl(-x))
    def el(x):
        assert abs(x)<50
        return down(expl(x) if x>=0 else 1/expu(-x))
    def logl(x):
        assert x>=1
        k=0
        while x>=2:x/=2;k+=1
        def core(x):
            z=(x-1)/(x+1)
            return sum(2*z**(2*j+1)/F(2*j+1) for j in range(24))
        return down(core(x)+k*core(F(2)))
    def coshmoment(m,E,x):
        A=(el(x)+el(-x))/2-1
        return m*logl(1+A/m)-E*x*x/2
    assert coshmoment(F(4),eu(F(1,25)),F(5,2))>F(1,100)
    rows=[(F(91,2000),F(947,100),F(47,50)**4+(1-F(47,50)**2)**2),
          (F(7,160),F(239,25),F(19,20)**4+(1-F(19,20)**2)**2),
          (F(19,500),F(10),F(1))]
    s=F(50,23);b=F(19,25);nu=F(9,2)
    for p,A,z in rows:
        P0=A*A/2+A*s+s*s;P1=6*(A+s);P2=F(18)
        assert P1-(1+b)*P0<0
        assert 2*P2-b*(P0+P1)<0
        assert P2-b*(P1+P2)<0
        # L<=51/50, using m4<=4 and the decreasing rare term.
        assert 4*(1+2*z)/6+p*P0-el(F(-1,25))/(2*F(51,50))<nu
    margins=[]
    for j in range(376,710):
        yl=F(j,1000);yh=F(j+1,1000);dl=yl**4;dh=yh**4;Ll=1+dl;Lh=1+dh
        c=3+F(9,2)*yh*yh-F(21,10)*yh**4-F(4,5)*yh**6
        E=eu(2*dh);m=up(c*E*Lh)
        xx=20*yh*(F(29,5)+3*yh*yh)
        n=(2*xx.numerator+xx.denominator)//(2*xx.denominator);x=F(n,20)
        assert coshmoment(m,E,x)>F(1,10000),(j,'moment')
        for p,A,z in rows:
            al=A+6*dl
            rare=p*eu(-b*dl)*(al*al/2+al*s+s*s)/Ll
            v=m*eu(-2*dl)*(1+2*z)/(6*Ll)+rare-el(-2*dh)/(2*Lh)
            assert v<nu,(j,v)
            margins.append(nu-v)
    assert F(376,1000)**4<F(1,50)
    assert F(710,1000)**4>F(1,4)
    # L>=5/4 is checked by check_tail_moment_cutoff.
    # Low-kappa tail formula is at most four: the same derivative argument.
    # -L² e^(2d) f' >= c*C0*L²+c*C1*L+C1-L-1/2.
    c=F(5,4);C0=F(5,21)*F(13,4);C1=F(10,21)
    assert c*(C0+C1)+C1-F(3,2)>0
    assert 2*c*C0+c*C1-1>0
    assert F(13,4)+C0+C1-F(1,2)==4
    assert F(25225,1296)<nu**2
    assert F(10896875,186624)<nu**3
    assert F(295,72)<nu
    assert min(margins)>F(1,125)
    print('PASS: general delta=3/2;334 fourth-moment cells, margin>1/125.')


def check_conditioning_example():
    """Certify the rounded-quartet sample sizes displayed in main.tex."""
    from math import isqrt

    def log_bounds(x, terms=80):
        z=(x-1)/(x+1)
        assert 0<=z<1
        lo=2*sum((z**(2*j+1)/F(2*j+1) for j in range(terms)),F(0))
        return lo,lo+2*z**(2*terms+1)/F(2*terms+1)/(1-z*z)

    def sqrt_bounds(x, denominator=10**20):
        m=isqrt(x.numerator*denominator**2//x.denominator)
        lo=F(m,denominator);hi=F(m+1,denominator)
        assert lo*lo<=x<hi*hi
        return lo,hi

    l2,h2=log_bounds(F(2));lr,hr=log_bounds(F(25,16))
    log_lo=7*l2+lr;log_hi=7*h2+hr
    nlo,nhi=sqrt_bounds(F(1000));tlo,_=sqrt_bounds(2*log_lo);_,thi=sqrt_bounds(2*log_hi)
    dlo,dhi=sqrt_bounds(F(2))
    for name,a,b,g,dl,dh,m in [('general',F(384,100),F(158,100),F(235,100),F(3,2),F(3,2),6455),('K=1',F(132,100),F(112,100),F(232,100),dlo,dhi,5500)]:
        lo=(4*nlo+3*a+g+(3*b+dl)*tlo)**2/4
        hi=(4*nhi+3*a+g+(3*b+dh)*thi)**2/4
        assert m-1<lo<hi<m
        print('PASS:',name,'strict real threshold lies between',m-1,'and',m,'; first sufficient integer',m)

if __name__ == '__main__':
    check_k_one_lower()
    check_determinants()
    check_k_one_upper_entropy()
    check_k_one_upper_mgf()
    check_tail_moment_cutoff()
    check_uniform_lower_plateau()
    check_uniform_lower_higher_moments()
    check_uniform_lower_beta()
    check_general_upper_second_moment()
    check_general_upper_tail_extension()
    check_general_I_cubic()
    check_general_upper_drift()
    check_conditioning_example()
    print('All exact arithmetic checks passed; this is not a formal proof.')
