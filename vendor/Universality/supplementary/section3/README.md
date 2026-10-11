# Section 3: the noncommuting witness

Run `python supplementary/section3/verify_permutation.py` from the repository root
with Python 3.11 or later. Only the standard library is required.

The program enumerates all 32 configurations of the Wheatstone rule and all
8192 configurations of its 13-edge extension. It checks crossing probabilities,
pivotal derivatives, both exact two-dimensional mass blocks, and the trace
difference `-1521/4194304` between the two fourfold products. This is the finite
calculation used in the manuscript's permutation-obstruction lemma; it does
not claim to verify all surrounding percolation theory.

`noncommuting-witness.tex` preserves the lemma and proof, and `figure/` contains
its TikZ figure. The LaTeX is a fragment using manuscript macros and references.
`verification.txt` records the rerun output. Optimized Python is rejected.

The script was copied from the manuscript, with only an optimization guard and
module description added. Mathematical computations are unchanged.
