# Building and source snapshots

This guide concerns the [historical supplement](HISTORICAL_SUPPLEMENT.md),
pending its later deletion. Do not update it to follow future Lean changes.
For current formalization setup and proof status, use
[lean/README.md](../lean/README.md) and [MIGRATION.md](MIGRATION.md). A successful
LaTeX build does not establish the complete canonical Lean targets.

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
from a successful [manual Supplement build run](https://github.com/marcusdavidwebb/SubGaussianTailBounds/actions/workflows/supplement.yml).

The hosted job installs the required LaTeX packages on its disposable Ubuntu
runner. It prefers Ubuntu's main HTTPS archive over the Azure mirror, with
bounded download timeouts and retries; installation is noninteractive.
Package installation and PDF compilation are separate steps in the job log,
so a download timeout can be distinguished from a document error. The same
document build and citation/reference/box checks run after installation.

For a hosted document-only test, use **Actions → Supplement build → Run
workflow** and select your branch. This optional historical-document job is separate from current Lean verification
and is not a required contribution check. See [CI policy](CI.md).

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

## Current Lean verification

For the maintained formalization, use the [pinned external Lean setup](../lean/README.md)
and run `./lean/verify.sh`. The historical supplement and its PDF build do not
participate in canonical theorem acceptance. Retired Python mathematical
checkers are described only in historical records and Git history.
