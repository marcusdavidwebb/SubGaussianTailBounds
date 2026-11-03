#!/usr/bin/env python3
"""Generate adaptive convex chords for the general upper-mean bound.

Search and generation use exact rational arithmetic. Every retained value and
margin is checked again by Lean's kernel in the generated sources. This script
is not a proof oracle.
The row parameters remain in KL/Upper/GeneralMeanCellData.lean.
"""
from __future__ import annotations

from fractions import Fraction as Q
from functools import cache
from pathlib import Path
import argparse
import re

ROOT = Path(__file__).resolve().parents[1]
CERT = ROOT / 'lean/SingularValueBounds/KL/Certificates'
SCALE = 10**15
FINAL_SCALE = 10**6


def floor(x: Q) -> int:
    return x.numerator // x.denominator


def down(x: Q) -> Q:
    return Q(floor(x*SCALE), SCALE)


def up(x: Q) -> Q:
    return -down(-x)


@cache
def log_unit(x: Q) -> tuple[Q, Q]:
    z = (x-1)/(x+1)
    lo, hi = down(z), up(z)
    zlo, zhi = down(lo*lo), up(hi*hi)
    lower = upper = Q(0)
    for j in range(18):
        lower += down(2*lo/(2*j+1))
        upper += up(2*hi/(2*j+1))
        lo, hi = down(lo*zlo), up(hi*zhi)
    return lower, upper+up(2*hi/(37*(1-zhi)))


@cache
def log_bounds(x: Q) -> tuple[Q, Q]:
    if x < 1:
        lo, hi = log_bounds(1/x)
        return -hi, -lo
    count = 0
    while x >= 2:
        count += 1
        x /= 2
    lo, hi = log_unit(x)
    l2, u2 = log_unit(Q(2))
    return lo+count*l2, hi+count*u2


@cache
def exp_upper(x: Q) -> Q:
    y = up(x)
    if y < 0:
        b = floor(-y*SCALE)
        term = total = SCALE
        for j in range(24):
            term = term*b//(SCALE*(j+1))
            total += term
        return up(Q(SCALE, total))
    b = floor(y*SCALE)
    term = total = SCALE
    for j in range(24):
        term = -((-term*b)//(SCALE*(j+1)))
        total += term
    return Q(total, SCALE)+up(up(Q(term, SCALE)*y/25)/(1-y/26))


def resolvent_lower(x: Q) -> Q:
    return (x*x+8*x+11)/(x**3+9*x*x+18*x+6)


def resolvent_upper(x: Q) -> Q:
    return (x**3+11*x*x+26*x+6)/(x*(x**3+12*x*x+36*x+24))


def qstr(x: Q) -> str:
    return str(x.numerator) if x.denominator == 1 else f'({x.numerator}/{x.denominator}:ℚ)'


def row_values(row: list[Q]):
    _, k, _, a, J, q, c, C = row
    argument = q/2+a/(2*k**3)*(-log_bounds(1-q*k*k)[0]-q*k*k)+C/(2*k*k)
    prefactor = exp_upper(argument)
    cutoff = Q(47,20)/(k*(q-1)) if q != 1 else Q(0)
    cutoff_log = log_bounds(cutoff/c)[1] if q > 1 else Q(0)

    @cache
    def error(j: int) -> Q:
        L = Q(j+40,40)
        value = (2*prefactor/q)*exp_upper(-2-(q*c/2-2)*L)*(1+resolvent_upper(q*c*L/2))
        if q > 1:
            value += prefactor*exp_upper(-2-(q*cutoff/2-2)*L)*(
                (2-2/q)*(1+cutoff_log)+2*resolvent_upper(cutoff*L/2)
                -(2/q)*resolvent_lower(q*cutoff*L/2))
        return Q(-floor(-value*FINAL_SCALE), FINAL_SCALE)

    def margin(j: int, kidx: int) -> Q:
        l, u = Q(j+40,40), Q(kidx+40,40)
        slope = (error(kidx)-error(j))/(u-l)
        rate = Q(7,20)-slope
        if rate <= 0:
            return Q(-1)
        point = min(u,max(l,1/rate))
        return 2+rate*point-log_bounds(c*point)[1]-J/2-error(j)+slope*l

    # A greedy longest passing chord leaves only a few intervals in each row.
    # The exact margin check, rather than a fixed precision target, determines
    # whether the proposed interval is sufficient for the displayed coefficient.
    nodes = [0]
    while nodes[-1] < 120:
        j = nodes[-1]
        kidx = j+1
        if margin(j,kidx) <= 0:
            raise ValueError(f'No passing chord at row {row}, index {j}')
        while kidx < 120 and margin(j,kidx+1) > Q(1,100000):
            kidx += 1
        nodes.append(kidx)
    assert all(margin(j,kidx) >= 0 for j,kidx in zip(nodes,nodes[1:]))
    assert 2+4*Q(7,20)-log_bounds(4*c)[1]-J/2-error(120) >= 0
    return prefactor, cutoff_log, nodes, error


IMPORTS = '''import SingularValueBounds.KL.Certificates.GeneralMeanPrefactorLogs
import SingularValueBounds.KL.Certificates.GeneralMeanNumericalAssembly
import SingularValueBounds.KL.Certificates.ConcreteGeneralMeanDomains
import SingularValueBounds.KL.Certificates.IntegerResolventEvaluation
import SingularValueBounds.KL.Certificates.IntegerRoundedExp
import SingularValueBounds.KL.Certificates.IntegerRoundedLog
import SingularValueBounds.KL.Certificates.RoundedLogTwo

set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 100000
'''
LOG_SIMP = '''  simp only [logRoundedQ, logPositiveRoundedQ, logReductionQ, natLog_two_eq_logTwoFuel]
  simp only [logUnitLowerQ_two, logUnitUpperQ_two]
  simp only [logUnitLowerQ_eq_int, logUnitUpperQ_eq_int]
'''


def render_row(index: int | None, row: list[Q]) -> tuple[str, int]:
    r = f'(generalMeanRows {index})' if index is not None else 'generalMeanSmallRow'
    ns = f'EntropyRow{index:04d}' if index is not None else 'SmallEntropyRow'
    prefactor, cutoff_log, nodes, error = row_values(row)
    text = f'\nnamespace SingularValueBounds.KL.Certificates.{ns}\nopen SingularValueBounds.KL.Certificates\n'
    text += f'private theorem prefactorValue : {r}.prefactor = {qstr(prefactor)} := by\n'
    text += '  simp only [GeneralMeanRow.prefactor, GeneralMeanRow.prefactorArgument, GeneralPrefactorLogs.lower_eq_cache]\n'
    text += '  simp only [generalMeanExpUpperQ_eq_integer]\n  decide +kernel\n\n'
    if row[5] > 1:
        text += f'private theorem cutoffLogValue : (logRoundedQ ({r}.cutoff/{r}.c)).2 = {qstr(cutoff_log)} := by\n'+LOG_SIMP+'  decide +kernel\n\n'
    text += f'private noncomputable def nodes : Fin {len(nodes)} → Fin 121 := !['+', '.join(map(str,nodes))+']\n'
    text += f'private noncomputable def values : Fin {len(nodes)} → ℚ := !['+', '.join(qstr(error(j)) for j in nodes)+']\n'
    text += f'''private theorem nodeValues (j : Fin {len(nodes)}) :
    {r}.error (generalMeanGrid (nodes j).val) = values j := by
  revert j
  simp only [GeneralMeanRow.error, GeneralMeanRow.rawError, prefactorValue'''
    text += ', cutoffLogValue]\n' if row[5]>1 else ']\n'
    text += '  simp only [generalMeanExpUpperQ_eq_integer, resolventUpperQ_eq_integer, resolventLowerQ_eq_integer]\n  decide +kernel\n\n'
    text += f'''private theorem segmentConditions (i : Fin {len(nodes)-1}) :
    let j := (nodes ⟨i.val,by omega⟩).val
    let k := (nodes ⟨i.val+1,by omega⟩).val
    0 < {r}.criticalRate j k ∧
    0 ≤ 2+{r}.criticalRate j k*{r}.criticalPoint j k-
      (logRoundedQ ({r}.c*{r}.criticalPoint j k)).2-{r}.J/2-
      {r}.error (generalMeanGrid j)+{r}.slope j k*generalMeanGrid j := by
  dsimp only
  simp only [GeneralMeanRow.criticalPoint, GeneralMeanRow.criticalRate, GeneralMeanRow.slope, nodeValues]
  revert i
'''+LOG_SIMP+'  decide +kernel\n\n'
    text += f'''private theorem finalMargin :
    0 ≤ 2+4*(47/20-2)-(logRoundedQ (4*{r}.c)).2-{r}.J/2-{r}.error 4 := by
  have he : {r}.error 4 = {qstr(error(120))} := by
    have hn := nodeValues ({len(nodes)-1} : Fin {len(nodes)})
    have hi : (nodes ({len(nodes)-1} : Fin {len(nodes)})).val = 120 := by decide +kernel
    have hv : values ({len(nodes)-1} : Fin {len(nodes)}) = {qstr(error(120))} := by decide +kernel
    rw [hi, hv, generalMeanGrid_last] at hn
    exact hn
  rw [he]
'''+LOG_SIMP+'  decide +kernel\n\n'
    intervals = '['+', '.join(f'({j},{k})' for j,k in zip(nodes,nodes[1:]))+']'
    text += f'theorem numerical : GeneralMeanNumericalConditions {r} := by\n'
    if index is not None:
        text += f'  apply generalMeanNumericalConditions_of_margins _ (generalMeanRows_basicDomains {index})\n    (generalMeanRows_prefactorDomain {index}) {intervals}\n'
    else:
        text += f'  apply generalMeanNumericalConditions_of_margins _ (by unfold GeneralMeanBasicDomains; decide +kernel)\n    (by decide +kernel) {intervals}\n'
    text += '  · simp only [GeneralMeanPartition]\n    decide +kernel\n'
    for projection in ['1','2']:
        text += '  · simp only [List.forall_mem_cons]\n'
        text += '    exact '+''.join(f'⟨(segmentConditions {n}).{projection}, ' for n in range(len(nodes)-1))+'List.forall_mem_nil _'+'⟩'*(len(nodes)-1)+'\n'
    text += '  · exact finalMargin\n'
    text += f'end SingularValueBounds.KL.Certificates.{ns}\n'
    return text,len(nodes)


def generate(blocks: int | None = None, *, check: bool = False) -> None:
    def emit(path: Path, text: str) -> None:
        if check:
            if path.read_text() != text:
                raise ValueError(f"Stale generated certificate: {path.relative_to(ROOT)}")
        else:
            path.write_text(text)

    source = (ROOT/'lean/SingularValueBounds/KL/Upper/GeneralMeanCellData.lean').read_text()
    tuples = re.findall(r'⟨((?:\([^()]+\),\s*){8})⟨\d+,by decide⟩⟩', source)
    rows = [[Q(x) for x in re.findall(r'\(([^()]+)\)', t)] for t in tuples]
    assert len(rows) == 1330
    total = 0
    for block in range(19 if blocks is None else blocks):
        text = IMPORTS+'\n/-! Adaptive convex chords for the general upper-mean entropy bound.\nGenerated by scripts/generate_general_mean.py; all witnesses are checked in Lean. -/\n'
        for index in range(70*block,70*(block+1)):
            row_text, count = render_row(index,rows[index])
            text += row_text
            total += count
        text += f'\nnamespace SingularValueBounds.KL.Certificates\ntheorem generalMeanEntropyBlock{block:02d} (j : Fin 70) :\n    GeneralMeanNumericalConditions (generalMeanRowBlocks {block} j) := by\n  fin_cases j\n'
        for index in range(70*block,70*(block+1)):
            text += f'  · exact EntropyRow{index:04d}.numerical\n'
        text += 'end SingularValueBounds.KL.Certificates\n'
        emit(CERT/f'ConcreteGeneralMeanEntropyRows/Block{block:02d}.lean', text)
        print(f'block {block:02d}: cumulative {total} nodes', flush=True)
    if blocks is None:
        text = 'import SingularValueBounds.KL.Upper.GeneralMeanCells\n'+IMPORTS
        small,count = render_row(None,list(map(Q,['0','2/5','0','2/5','257/120','11/4','193/100','79/10000'])))
        text += small+'\nnamespace SingularValueBounds.KL.Certificates\ntheorem generalMeanSmallRow_numerical : GeneralMeanNumericalConditions generalMeanSmallRow :=\n  SmallEntropyRow.numerical\nend SingularValueBounds.KL.Certificates\n'
        emit(CERT/'ConcreteGeneralMeanSmall.lean', text)
        print(f'total: {total+count} nodes, {total+count-1331} intervals',flush=True)


if __name__ == '__main__':
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--blocks',type=int,help='generate only this many initial blocks for a pilot')
    parser.add_argument('--check', action='store_true', help='Reject stale generated sources without writing.')
    args = parser.parse_args()
    generate(args.blocks, check=args.check)
