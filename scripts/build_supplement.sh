#!/usr/bin/env bash
set -euo pipefail
supplement_root="$(cd "$(dirname "$0")/.." && pwd -P)"
if [[ -f "$supplement_root/../main.tex" ]]; then
  cd "$supplement_root/.."
  latexmk -pdf -synctex=1 -interaction=nonstopmode -halt-on-error -quiet main.tex
  latexmk -pdf -synctex=1 -interaction=nonstopmode -halt-on-error -quiet \
    -outdir=supplementary supplementary/supplementary.tex
  supplement_log="$supplement_root/../build/latex/supplementary.log"
else
  cd "$supplement_root"
  latexmk -pdf -synctex=1 -interaction=nonstopmode -halt-on-error -quiet supplementary.tex
  supplement_log="$supplement_root/build/latex/supplementary.log"
fi
python3 - "$supplement_log" <<'PY'
from pathlib import Path
import re
import sys

log = Path(sys.argv[1])
if not log.is_file():
    raise SystemExit(f"Missing final supplement log: {log}")
patterns = (
    r"(?:LaTeX|Package \S+) Warning: (?:Reference|Citation) .*undefined",
    r"There were undefined (?:references|citations)",
    r"Label\(s\) may have changed",
    r"(?:Overfull|Underfull) \\[hv]box",
)
issues = [line for line in log.read_text(errors="replace").splitlines()
          if any(re.search(pattern, line) for pattern in patterns)]
if issues:
    raise SystemExit("Supplement log requires attention:\n" + "\n".join(issues))
print("PASS: supplementary PDF built with resolved references/citations and no box warnings.")
PY
