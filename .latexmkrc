# Use XeLaTeX for the Unicode Lean statement, including editor recipes using -pdf.
$pdf_mode = 1;
# Keep only the requested PDF even when an editor passes -synctex=1/-outdir=.
$pdflatex = 'xelatex %O -no-shell-escape -synctex=0 %S';
$xelatex = $pdflatex;

# Build outside the checkout, copy back only the PDF, and remove auxiliary files
# when latexmk exits. In -pvc mode the temporary directory lasts for the watcher.
use File::Temp qw(tempdir);
$out_dir = tempdir('subgaussian-latexmk-XXXXXX', TMPDIR => 1, CLEANUP => 1);
$aux_dir = $out_dir;
$out2_dir = '.';
@out2_exts = ('pdf');
