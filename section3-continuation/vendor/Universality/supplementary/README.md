# Supplementary materials for IGS Bernoulli percolation and universality

This directory collects reproducible calculations and construction details
for the manuscript. It complements the separate Lean development in this
repository; passing a Python checker is not a claim of complete Lean coverage.

| Material | Role | Contents |
|---|---|---|
| [Section 3](section3/README.md) | Current paper | Exhaustive noncommuting-witness calculation, exact output, proof fragment and TikZ figure |
| [Section 5](section5/README.md) | Current paper | Complete allocation construction, eight data files, independent integer verifiers and outputs |
| [Spectral perturbation](additional/spectrum/README.md) | Additional example removed from the main text | Preserved proof, finite capacity and spectral checks, output |
| [Finite-rank constants](additional/finite-rank/README.md) | Historical material omitted from the paper | Old argument and finite constant checker; no claim that the checker proves the full theorem |

Each folder gives its run commands and precise verification scope. Scripts use
Python 3.11 or later and the standard library; run without `-O` or `-OO`.
The existing Section 5 input data are shared rather than duplicated.
`provenance.json` records the sources and hashes of this supplementary upload.

The repository remains private. A reviewer will need repository access or an
export of the supplementary directory. Manuscript links to an immutable
Section 5 commit continue to identify that original verified snapshot.
