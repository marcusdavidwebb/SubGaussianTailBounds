# Substantial contributions

This ledger preserves substantial mathematical, certificate and formalisation
credit independently of Git merge style. It does not establish priority,
novelty or future paper authorship. Keep old entries when work is superseded or
corrected, and add explicit links to the later assessment.

## Baseline supplementary proof and hybrid verification

- **Responsibility and credit:** Marcus Webb is the sole author of the
  supplementary document and takes full responsibility. Its entire proof and
  exposition were AI-generated without direct input from him. The accompanying
  paper is by Marcus Webb and Morgan Lynch-Davies, whose extensive preceding
  mathematical work yielded weaker bounds. Section S2 preserves this account
  and the roles of the models, Lean and Python.
- **Results:** [baseline-general](contributions/records/baseline-general.json),
  `(96/25,79/50,47/20,3/2)` for every $K\ge1$, and
  [baseline-one](contributions/records/baseline-one.json),
  `(33/25,28/25,58/25,sqrt(2))` at $K=1$.
- **Evidence:** [written proof](supplementary.tex),
  [Lean result](lean/SingularValueBounds/KL/Theorem.lean),
  [original checker](check_main_constants.py), interface runners,
  [proof/certificate map](lean/FORMALISATION_PLAN.md) and
  [verification report](lean/VERIFICATION_REPORT.md).
- **Status:** completed hybrid verification observed on 20 October 2026, after
  retirement of the standalone earlier theorem. Lean checks the analytic
  implication; Python checks the finite conditions outside Lean. This is not
  an unconditional kernel proof of those conditions.
- **History:** source inventories, assisted timings, cleanup and validation
  scope remain in the original verification records. There is no public PR,
  commit or release identifier yet; this ledger does not invent earlier public
  Git history.

## Later substantial contributions

At preparation time, no later contribution had been accepted.
Append later entries below without editing earlier ledger text. Include each
ID, contributors, date, exact result/regime,
predecessor or supersession, evidence, review decision and actual public links.
Follow [CONTRIBUTING.md](CONTRIBUTING.md).
