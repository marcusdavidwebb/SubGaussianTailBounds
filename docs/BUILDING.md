# Building and source snapshots

## Standalone repository

From a checkout of
[SubGaussianTailBounds](https://github.com/marcusdavidwebb/SubGaussianTailBounds),
run the following at the repository root with an existing LaTeX installation
providing `latexmk`, pdfLaTeX, BibTeX and the document's packages:

```sh
./scripts/build_supplement.sh
```

The helper rejects unresolved citations/references and box warnings in the
final log. A successful run exits with status 0 and ends with:

```text
PASS: supplementary PDF built with resolved references/citations and no box warnings.
```

The equivalent build command, before that log check, is:

```sh
latexmk -pdf -synctex=1 -interaction=nonstopmode -halt-on-error -quiet supplementary.tex
```

The local `.latexmkrc` keeps intermediates under `build/latex/` and the readable
`supplementary.pdf` beside its source. SyncTeX and intermediates are ignored.
Inspect changed pages after layout changes.

Without a local LaTeX installation, read the checked-in
[supplementary PDF](../supplementary.pdf), or download the PDF and build log
from a successful [GitHub verification run](../lean/README.md#verification-on-github).

The root `references.bib` snapshots the parent paper's shared bibliography.
`docs/main-labels.tex` contains the five referenced main-paper label numbers.
Standalone references are unlinked because the in-preparation paper/PDF are
not included. The supplementary theorem statement is self-contained.

## Original paper checkout

Run from the paper repository root, preserving the main-first dependency:

```sh
latexmk -pdf -synctex=1 -interaction=nonstopmode -halt-on-error -quiet main.tex
latexmk -pdf -synctex=1 -interaction=nonstopmode -halt-on-error -quiet -outdir=supplementary supplementary/supplementary.tex
```

This mode imports live `build/latex/main.aux`, uses the shared bibliography and
preserves PDF links. The main paper builds without supplement auxiliary files.

After label or shared bibliography changes, refresh the public snapshots from
the supplementary folder:

```sh
python3 scripts/sync_paper_assets.py --paper-root ..
```

In a standalone checkout pass the actual existing paper checkout path. The
script reads its built auxiliary file and bibliography; it installs/downloads
nothing. Review the diff and rebuild affected documents. Do not invent labels
when the source paper is unavailable.

## Lean and exact arithmetic

For finite arithmetic checks, Python 3.11 or later and Bash are sufficient;
the checkers use only the Python standard library. From the repository root:

```sh
./lean/check_certificates.sh
```

For the complete hybrid checks, first configure an
[existing pinned Lean environment](../lean/README.md#pinned-environment-and-storage),
then run:

```sh
./lean/check_hybrid.sh
```

The hybrid wrapper validates the contribution registry, generates and checks
its claimed theorem targets, builds and audits Lean, and runs the original
and eleven interface checkers. For only the Lean build and audit, use
`./lean/check.sh`. See [the verification guide](../lean/README.md#verify) for
expected success messages and [GitHub Actions](../lean/README.md#verification-on-github)
for verification without local Lean. Local wrappers preserve pinned versions
and do not download dependencies. Keep Python assertions enabled.

Pull requests also require comparison with their base revision and any
applicable maintainer authorization. Follow
[contributions/README.md](../contributions/README.md) for those checks;
verifying the current registry alone does not enforce PR completeness.
