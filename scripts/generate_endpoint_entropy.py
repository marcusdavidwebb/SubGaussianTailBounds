#!/usr/bin/env python3
"""Generate exact certificates for analytic endpoint entropy integrals.

The retained rational partitions and corner majorants are numerical witnesses.
All domains, coverage, evaluations and inequalities are rechecked by Lean.
Only required logarithms are cached; no uniform quadrature or decay states remain.
"""
from __future__ import annotations
import argparse
from fractions import Fraction as Q
from pathlib import Path
import re
from functools import cache
import sys
sys.dont_write_bytecode = True
import generate_general_mean as arithmetic

ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / 'lean/SingularValueBounds/KL/Certificates'
UPPER = ROOT / 'lean/SingularValueBounds/KL/Upper'
SCALE = 10**15


def qstr(x: Q) -> str:
    return f'({x.numerator}/{x.denominator}:ℚ)'


def lookup(values: dict[int, int]) -> str:
    pairs = sorted(values.items())
    def go(items):
        if len(items) == 1: return f'(.leaf ({items[0][1]}:ℤ))'
        mid = len(items)//2
        return f'(.branch {items[mid][0]} {go(items[:mid])} {go(items[mid:])})'
    return go(pairs)


def log_tree(values: dict[Q, int]) -> str:
    pairs = sorted(values.items())
    def go(items):
        if not items: return '.empty'
        mid = len(items)//2
        x, value = items[mid]
        return f'(.node {qstr(x)} ({value}:ℤ) {go(items[:mid])} {go(items[mid+1:])})'
    return go(pairs)


@cache
def primitive_upper(c: Q, q: Q, u: Q) -> Q:
    return (2/q)*arithmetic.exp_upper(-q*u/2)*(1+arithmetic.log_bounds(u)[1]-
        arithmetic.log_bounds(c)[0]+arithmetic.resolvent_upper(q*u/2))


@cache
def primitive_lower(c: Q, q: Q, u: Q) -> Q:
    if q*u/2 >= 24: return Q(0)
    return (2/q)/arithmetic.exp_upper(q*u/2)*(1+max(Q(0),arithmetic.log_bounds(u)[0]-
        arithmetic.log_bounds(c)[1])+arithmetic.resolvent_lower(q*u/2))


def weight(c: Q, q: Q, a: Q, b: Q) -> Q:
    value = primitive_upper(c,q,a)-primitive_lower(c,q,b)
    return Q(-arithmetic.floor(-value*10**10),10**10)


def inputs():
    data = (UPPER/'EndpointMeanData.lean').read_text()
    points_text = data.split('noncomputable def endpointMeanAPoint ',1)[1].split('noncomputable def endpointMeanCornerData',1)[0]
    points = {int(i):Q(v.strip().strip('()')) for i,v in re.findall(r'\| (\d+) => ([^\n]+)',points_text)}
    points[42] = Q(1)
    pattern = r'\| (\d+),(\d+) => \(\(\(([^)]+)\),\(([^)]+)\),\(([^)]+)\),\(([^)]+)\)\),(\d+),(\d+)\)'
    corners = {(int(k),int(a)):(list(map(Q,fields[:4])),int(fields[5])) for k,a,*fields in re.findall(pattern,data)}
    run_data = (UPPER/'EndpointEntropyRunData.lean').read_text()
    joint_text,small_text = run_data.split('noncomputable def endpointSmallRuns',1)
    runs = {(int(k),int(a)):[tuple(map(int,z)) for z in re.findall(r'⟨(\d+),(\d+),(\d+)⟩',rs)]
            for k,a,rs in re.findall(r'\| (\d+),(\d+) => (\[[^\n]+\])',joint_text)}
    small = {int(i):[tuple(map(int,z)) for z in re.findall(r'⟨(\d+),(\d+),(\d+)⟩',rs)]
             for i,rs in re.findall(r'\| (\d+) => (\[[^\n]+\])',small_text)}
    assert len(corners)==len(runs)==837 and len(small)==50
    return points,corners,runs,small


IMPORTS = '''import SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
import SingularValueBounds.KL.Certificates.IntegerLookupTree
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace SingularValueBounds.KL.Certificates
'''

SIMP = '''  simp only [EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq]
  try simp only [generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer,resolventLowerQ_eq_integer]
'''


def render(points,corners,runs,small, limit=None):
    lower,upper = {},{}
    files = {}
    blocks = ['' for _ in range(10)]
    small_source = ''
    metrics = {'joint_intervals':sum(map(len,runs.values())),'small_intervals':sum(map(len,small.values()))}
    jobs = [(False,key,rs) for key,rs in sorted(runs.items())]+[(True,i,rs) for i,rs in sorted(small.items())]
    for is_small,key,rs in jobs:
        if limit is not None and (is_small or key != (0,0)):continue
        if is_small:
            i=key;j0=rs[0][0];k=Q(i+1,200);targets=[Q(239,200)+Q(9,20)*i*i/200**2+Q(i**4,2*200**4)]
            shapes=[(k,None)];params=str(i);kind='Small';rs_expr=f'endpointSmallRuns {i}';cut=f'endpointSmallCutoff {i}'
        else:
            ki,ai=key;targets,j0=corners[key];bottom,top=Q(ki+20,80),Q(ki+21,80)
            left,right=max(points[ai],bottom**3),points[ai+1]
            shapes=[(bottom,left),(bottom,right),(top,left),(top,right)];params=f'{ki} {ai}';kind='Joint';rs_expr=f'endpointMeanRuns {params}';cut=f'endpointMeanCutoff {params}';k=top
        c=Q(j0,200);weights={};prefactors=[{} for _ in shapes]
        for a,b,qi in rs:
            q=Q(qi,100);u,v=Q(max(j0,a-1),200),Q(max(j0,b-1),200)
            assert j0<=a<b<=8000 and 90<=qi<=200 and q*k*k<1 and v*k*(q-1)<=Q(58,25)
            weights[a]=int(weight(c,q,u,v)*SCALE)
            assert Q(weights[a],SCALE)>=0
            for point in [c,u,v]:
                lo,hi=arithmetic.log_bounds(point);lower[point]=int(lo*SCALE);upper[point]=int(hi*SCALE)
            for h,(kh,ah) in enumerate(shapes):
                argx=1-q*kh*kh
                lo=arithmetic.log_bounds(argx)[0];lower[argx]=int(lo*SCALE)
                arg=(-lo/(2*kh*kh)) if is_small else q/2+ah*(-lo-q*kh*kh)/(2*kh**3)
                assert arithmetic.up(arg)<26
                prefactors[h][qi]=int(arithmetic.exp_upper(arg)*SCALE)
        end=Q(max(j0,7999),200);lo,hi=arithmetic.log_bounds(end);lower[end]=int(lo*SCALE);upper[end]=int(hi*SCALE)
        tail=arithmetic.up(Q(31623,10000)*primitive_upper(c,Q(9,10),end))
        totals=[arithmetic.log_bounds(c)[1]+tail+sum(Q(weights[a],SCALE)*Q(prefactors[h][q],SCALE) for a,b,q in rs) for h in range(len(shapes))]
        assert all(v<=t for v,t in zip(totals,targets)),(key,totals,targets)
        ns=f'EndpointAnalytic{kind}'+(f'{key:02d}' if is_small else f'{key[0]:02d}_{key[1]:02d}')
        text=f'\nnamespace {ns}\n'
        text+=f'private noncomputable def weights : IntegerLookupTree := {lookup(weights)}\n'
        if is_small:
            text+=f'private noncomputable def prefactors : IntegerLookupTree := {lookup(prefactors[0])}\n'
            pref_expr='prefactors.get r.rate';pred=f'EndpointSmallNumericalConditions {params}'
        else:
            trees=', '.join(lookup(pref) for pref in prefactors)
            text+=f'private noncomputable def prefactors : Fin 4 → IntegerLookupTree := ![{trees}]\n'
            pref_expr='(prefactors h).get r.rate';pred=f'EndpointJointNumericalConditions {params}'
        text+=f'private theorem cover : EndpointRunsCover ({cut}) 8000 ({rs_expr}) := by decide +kernel\n'
        text+=f'private theorem domains : ∀r∈{rs_expr}, EndpointRunConditions ({cut}) '+(f'(endpointSmallK {params})' if is_small else f'(endpointMeanBox {params}).top')+' r := by\n  simp only [EndpointRunConditions]\n  decide +kernel\n'
        quant='' if is_small else '∀h : Fin 4, '
        arg=f'endpointSmall24Argument (endpointSmallK {params}) ((r.rate:ℚ)/100)' if is_small else f'endpointJoint24Argument (endpointMeanCornerK {params} h) (endpointMeanCornerA {params} h) ((r.rate:ℚ)/100)'
        pref=f'endpointSmall24Q (endpointSmallK {params}) ((r.rate:ℚ)/100)' if is_small else f'endpointJoint24Q (endpointMeanCornerK {params} h) (endpointMeanCornerA {params} h) ((r.rate:ℚ)/100)'
        text+=f'private theorem prefactorDomains : {quant}∀r∈{rs_expr}, roundUpQ ({arg})<26 := by\n'
        text+='  simp only ['+('endpointSmall24Argument' if is_small else 'endpointJoint24Argument')+',EndpointAnalyticLogs.lower_eq]\n  decide +kernel\n'
        text+=f'private theorem prefactorValues : {quant}∀r∈{rs_expr}, {pref} = fixedQ ({pref_expr}) := by\n'
        text+='  simp only ['+('endpointSmall24Q,endpointSmall24Argument' if is_small else 'endpointJoint24Q,endpointJoint24Argument')+',EndpointAnalyticLogs.lower_eq,generalMeanExpUpperQ_eq_integer]\n  decide +kernel\n'
        text+=f'private theorem weightValues : ∀r∈{rs_expr}, endpointRunWeightQ ({cut}) r = fixedQ (weights.get r.start) := by\n'
        text+='  simp only [endpointRunWeightQ,entropyExpWeightUpperQ,primitiveUpperQ,primitiveLowerQ]\n'+SIMP+'  decide +kernel\n'
        text+=f'private theorem tailValue : endpointAnalyticTailQ ({cut}) = {qstr(tail)} := by\n'
        text+='  simp only [endpointAnalyticTailQ,primitiveUpperQ,EndpointAnalyticLogs.lower_eq,EndpointAnalyticLogs.upper_eq,generalMeanExpUpperQ_eq_integer,resolventUpperQ_eq_integer]\n  decide +kernel\n'
        numeric=f'endpointSmallNumeric {params}≤endpointSmallTarget {params}' if is_small else f'∀h : Fin 4, endpointMeanNumericCorner {params} h≤endpointMeanCorner {params} h'
        numexpr=f'endpointSmallNumeric {params}' if is_small else f'endpointMeanNumericCorner {params} h'
        logexpr=f'(logRoundedQ (({cut}:ℚ)/200)).2'
        expected=f'{logexpr}+{qstr(tail)}+(({rs_expr}).map (fun r => fixedQ (weights.get r.start)*fixedQ ({pref_expr}))).sum'
        text+=f'private theorem totalValue : {quant}{numexpr} = {expected} := by\n'
        if not is_small:text+='  intro h\n'
        text+=f'  have hm : ({rs_expr}).map (fun r => endpointRunWeightQ ({cut}) r*{pref}) =\n'
        text+=f'      ({rs_expr}).map (fun r => fixedQ (weights.get r.start)*fixedQ ({pref_expr})) := by\n'
        text+='    apply List.map_congr_left\n    intro r hr\n    rw [weightValues r hr,prefactorValues'+(' r hr' if is_small else ' h r hr')+']\n'
        text+='  unfold '+('endpointSmallNumeric' if is_small else 'endpointMeanNumericCorner')+'\n  rw [hm,tailValue]\n'
        text+=f'private theorem totals : {numeric} := by\n'
        text+='  simp only [totalValue,EndpointAnalyticLogs.upper_eq]\n  decide +kernel\n'
        text+=f'theorem conditions : {pred} := ⟨cover,domains,prefactorDomains,totals⟩\n'
        text+=f'end {ns}\n'
        if is_small:small_source+=text
        else:blocks[key[0]//6]+=text
    if limit is None:
        for ki in range(60):
            indices = sorted(ai for k,ai in corners if k==ki)
            body = (f'\nprivate theorem activeIndices{ki:02d} : ∀ai : Fin 42, endpointMeanActive {ki} ai → ai∈\n'
                    f'    ([{", ".join(map(str,indices))}] : List (Fin 42)) := by\n'
                    '  simp only [endpointMeanActive]\n  decide +kernel\n'
                    f'theorem endpointAnalyticRow{ki:02d} (ai : Fin 42) : endpointMeanActive {ki} ai →\n'
                    f'    EndpointJointNumericalConditions {ki} ai := by\n'
                    f'  intro hact\n  have hi := activeIndices{ki:02d} ai hact\n  fin_cases hi\n')
            body += ''.join(f'  · exact EndpointAnalyticJoint{ki:02d}_{ai:02d}.conditions\n' for ai in indices)
            blocks[ki//6] += body
        assembly = ''.join(f'import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Block{b:02d}\n' for b in range(10))
        assembly += 'import SingularValueBounds.KL.Certificates.EndpointAnalyticBlocks.Small\n\nnamespace SingularValueBounds.KL.Certificates\n'
        assembly += 'theorem endpointMean_analytic (ki : Fin 60) (ai : Fin 42) : endpointMeanActive ki ai →\n    EndpointJointNumericalConditions ki ai := by\n  revert ki ai\n'
        assembly += '  exact Fin.cases (motive := fun ki => ∀ai : Fin 42, endpointMeanActive ki ai →\n    EndpointJointNumericalConditions ki ai) endpointAnalyticRow00 <|\n'
        assembly += ''.join(f'    Fin.cases endpointAnalyticRow{i:02d} <|\n' for i in range(1,60))
        assembly += '    fun ki => Fin.elim0 ki\n\n'
        assembly += 'theorem endpointSmall_analytic (i : Fin 50) : EndpointSmallNumericalConditions i := by\n  fin_cases i\n'
        assembly += ''.join(f'  · exact EndpointAnalyticSmall{i:02d}.conditions\n' for i in range(50))
        assembly += '\nend SingularValueBounds.KL.Certificates\n'
        files[CERT/'ConcreteEndpointAnalytic.lean'] = assembly
    # Checked caches are exact evaluation shortcuts; every entry is independently validated.
    text='''import SingularValueBounds.KL.Upper.EndpointMeanFinite
import SingularValueBounds.KL.Certificates.RoundedLogCache
namespace SingularValueBounds.KL.Certificates.EndpointAnalyticLogs
set_option maxHeartbeats 0
set_option maxRecDepth 100000
'''
    for name,values,flag in [('lower',lower,'false'),('upper',upper,'true')]:
        text+=f'private noncomputable def {name} : RoundedLogCache := {log_tree(values)}\n'
        text+=f'private theorem {name}_valid : {name}.valid {flag} = true := by decide +kernel\n'
        component='1' if name=='lower' else '2'
        text+=f'theorem {name}_eq (x : ℚ) : (logRoundedQ x).{component} = {name}.get {flag} x := by\n'
        text+=f'  rw [logRoundedQ_eq_integer,integerLog_{name}_eq_cache {name} {name}_valid]\n'
    text+='end SingularValueBounds.KL.Certificates.EndpointAnalyticLogs\n'
    files[CERT/'EndpointAnalyticLogs.lean']=text
    for block,body in enumerate(blocks):
        if body:files[CERT/f'EndpointAnalyticBlocks/Block{block:02d}.lean']=IMPORTS+body+'\nend SingularValueBounds.KL.Certificates\n'
    if small_source:files[CERT/'EndpointAnalyticBlocks/Small.lean']=IMPORTS+small_source+'\nend SingularValueBounds.KL.Certificates\n'
    metrics.update(lower_log_values=len(lower),upper_log_values=len(upper))
    return files,metrics


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check',action='store_true')
    parser.add_argument('--pilot',action='store_true')
    args=parser.parse_args()
    files,metrics=render(*inputs(),limit=args.pilot or None)
    for path,content in files.items():
        if args.check:
            if path.read_text()!=content:raise SystemExit(f'Stale generated certificate: {path.relative_to(ROOT)}')
        else:
            path.parent.mkdir(parents=True,exist_ok=True);path.write_text(content)
    print(metrics,flush=True)
    print(f'{"Checked" if args.check else "Generated"} {len(files)} analytic entropy modules.')

if __name__=='__main__':main()
