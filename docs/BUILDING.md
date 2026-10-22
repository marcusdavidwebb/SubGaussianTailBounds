# Building and source snapshots

## Standalone repository

Copy the folder's contents to the new repository root. With an existing LaTeX
installation providing `latexmk`, pdfLaTeX, BibTeX and the document's packages:

```sh
./scripts/build_supplement.sh
```

The helper rejects unresolved citations/references and box warnings in the final
log. The equivalent build command, before that log check, is:

```sh
latexmk -pdf -synctex=1 -interaction=nonstopmode -halt-on-error -quiet supplementary.tex
```

The local `.latexmkrc` keeps intermediates under `build/latex/` and the readable
`supplementary.pdf` beside its source. SyncTeX and intermediates are ignored.
Inspect changed pages after layout changes.

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

See [lean/README.md](../lean/README.md) for the pinned external workspace.
From the public repository root:

```sh
./lean/check.sh
./lean/check_certificates.sh
./lean/check_hybrid.sh
```

These respectively build/audit Lean, run the original and eleven interface
checkers, and combine both. The contribution gate adds checks for each newly
claimed quartet; see [contributions/README.md](../contributions/README.md).
Python assertions must remain enabled.
