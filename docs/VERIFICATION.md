# Verification

`./lean/check-statements.sh` and `./lean/verify.sh` share one specification:
`SubGaussian.Current.general.{u}` and `SubGaussian.Current.unit.{u}` must have the
complete root propositions at the exact coefficients in `Canonical/Constants.lean`.
Their checked declaration types must be definitionally equal to independently
elaborated expected types, with the same universe parameters. A restricted
sample-space universe, conditional result or implication from unresolved numerical
premises is insufficient.

Expected types are elaborated before implementation imports. The runtime auditor
loads actual private declaration bodies with imported extensions disabled, so
candidate syntax and cached axiom summaries cannot replace the checks. It scans
actual logical dependencies and permits only `propext`, `Classical.choice` and
`Quot.sound`; unsafe or partial declarations cannot supply logical premises.

The focused command builds the two results' import closure with bounded module
concurrency, then checks exact types, universes and transitive axioms. It trusts
compiled imports. The full command additionally enumerates every maintained
source, builds the umbrella module, and independently replays each module's
logical declarations through upstream `Lean.Replay`. Dependencies are replayed
first, then their unchanged artifacts may seed later workers. The scheduler binds
artifact identities, checks collisions, rejects unsupported split project
artifacts and checks complete source/umbrella coverage. Generated auditor/specification
modules are checked too; no candidate proof module is silently treated as pinned.

Sources, setup/configuration, generators and verifier inputs are hashed before
and after a run. This detects changes during verification, including same-size
edits with unchanged timestamps; hashes and Python establish no mathematical
truth. The successful report describes the actual checked inputs. Build traces
may avoid recompilation; independent replay always runs afresh in the full mode.
The root statement has no fixed expected hash: edits are allowed, its README copy
must match, and verification checks proofs against the current root propositions.

Run the full command on the final relevant source state before merging. Keep
logs outside the checkout and report any interruption or failure honestly.
Marcus reviews the proof, coefficient changes, imported-definition changes and
verification-policy changes. Git supplies the previous result; there is no
accepted-constants snapshot, `SVB_TRUSTED_ROOT` or generated comparison protocol.
An agent may run all local checks, but needs explicit approval for a particular
PR and must never merge or enable automatic merging.

CI is one read-only administrative job: source presentation, generated-document
synchronization, attribution presence and Python regression tests. It installs
no Lean toolchain and performs no full Lean verification. A green CI status is
not proof verification. Local opt-in tests exercise exact-type, universe and
axiom rejection and independent kernel replay on small examples. Ordinary tests
cover source coverage, input identity and the supporting scripts.

See [setup](../lean/README.md), [performance](PERFORMANCE.md) and the historical
verification scope in [CONTRIBUTIONS.md](../CONTRIBUTIONS.md).
