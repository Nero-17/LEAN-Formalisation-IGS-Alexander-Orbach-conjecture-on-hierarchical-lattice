# Exact certificates for the Section 5 counterexamples

This supplement contains the complete symbolic construction, allocation data,
and independent integer checkers for the counterexamples in *Iterated Graph
Systems (II): Bernoulli percolation and universality class on hierarchical
lattices*. The implementation details moved out of the main text are preserved
in [construction-and-certificate-details.tex](construction-and-certificate-details.tex).
That archival fragment includes the graph grammar, the four target identities,
the initial allocation, the signed corrections, their disjoint supports,
capacity checks, and the deduction of the two main examples. It uses the
manuscript's macros and references and is not a standalone LaTeX document.

## Reproduce the verification

The compressed manuscript keeps the Wheatstone operation, its response
recursions, the three-state kernels, and the four target constraints. The
allocation encoding and its complete proof remain in
`construction-and-certificate-details.tex`; no separate supplementary PDF is
required. Labels in that unabridged source identify the formulas independently
of subsequent manuscript numbering.

The construction has three steps:

1. Expand a finite ternary tree of Wheatstone operations and decorate selected
   leaves by another Wheatstone rule. Binary projections of leaf addresses
   encode the allocation. Symbolic slots and physical copies have different
   multiplicities; the source derives both explicitly.
2. Preserve the all-outer allocation and the totals at each zero count while
   redistributing decorations. This preserves length, volume and pivotal
   response. Ordered mass kernels distinguish these redistributions. Signed
   correction packets adjust the mass action, and separate capacity checks
   ensure that every final allocation specifies an actual graph.
3. Verify the positive eigenvector `(55,46,23)`. This identifies the mass
   Perron root and makes it multiplicative for compositions of the certified
   seeds. The manuscript then proves the infinite incommensurate family.

### From the manuscript to the files

| Mathematical claim | Source or entry point |
|---|---|
| Allocation definition, response formulas, integer targets and correction packets | [Unabridged construction](construction-and-certificate-details.tex) |
| All four allocation inputs | The `word_base.json` and `packet_repair.json` files in the four directories listed below |
| Kernel enumeration, ordered matrix sums and capacity coverage | [Integer verifier](certificates/verify.py) |
| Shifted-scale verification | [Shifted verifier](certificates/verify_transcendental.py) |
| Exact certificates for the actual three seed rules | [SeedCertificates.lean](../../Universality/Section5/SeedCertificates.lean), [Seed19.lean](../../Universality/Section5/Seed19.lean), [Seed739.lean](../../Universality/Section5/Seed739.lean) |
| Actual shifted rule | [SeedShifted19.lean](../../Universality/Section5/SeedShifted19.lean) |
| Actual physical exponents and equality of classes | [CertifiedConsequences.lean](../../Universality/Section5/CertifiedConsequences.lean) |
| Pairwise incommensurability of the infinite family | `certifiedFamily_incommensurate` in [SeedCertificates.lean](../../Universality/Section5/SeedCertificates.lean) |

For the integrated Lean build and kernel audit, follow the repository's
[build instructions](../../docs/BUILD.md). The commands below independently check
the certificate arithmetic and do not require Lean.

From this directory, using Python 3.11 or later (standard library only):

```sh
python certificates/verify.py
python certificates/verify_transcendental.py
```

Do not use Python's `-O` or `-OO` options: the checks use assertions and the
verifier rejects optimized execution. No network, random input, numerical
tolerance, external package, or program that generated the data is required.

| Input directory | Base | Depth | Length scale |
|---|---:|---:|---|
| `certificates/n424` | 19 | 424 | 19^100 |
| `certificates/n936` | 661 | 936 | 661^100 |
| `certificates/n952` | 739 | 952 | 739^100 |
| `certificates/transcendental` | 19 | 424 | 19^100 + 480 |

Every input directory contains `word_base.json` and `packet_repair.json`.
For each row the edge count, mass Perron root, and pivotal multiplier are,
respectively, base^232, base^219, and base^70. The positive three-state mass
eigenvector is (55,46,23). The fourth row changes the scale and has different
allocation data; it is not obtained by changing only a displayed parameter.

The verifier reconstructs the kernels by enumerating all 32 Wheatstone
configurations, sums ordered matrix products exactly, and checks all allocation
capacities through disjoint-support bounds and explicit exceptional words.
The raw enormous graphs need not be expanded: the construction and the eight
input files specify finite graphs exactly.

Outputs are `certificates/verification.json` and
`certificates/transcendental-verification.json`. They include the checked
identities, coverage information, and SHA-256 hashes of the inputs.
The local `.gitattributes` preserves the input JSON bytes across checkouts,
so Git line-ending conversion cannot change these input hashes.

## Provenance and limits

The construction fragment and all input/checker files were copied without
mathematical changes from Overleaf project `69b4d5f8e9e9b26ffd015f17`, commit
`1b194c68cc1b1cefc73c0126c192c0e59a464b5b`, on 6 October 2026.
The output files in this supplement are generated by rerunning the commands
above after relocation.

These Python checks provide an independent arithmetic implementation. The
actual graph constructions and the four exact certificates are also proved in
the integrated Lean development; see [coverage](../../docs/COVERAGE.md). The final transcendental-dimension example is a single lattice;
it does not exhibit an incommensurate pair in a class with nonrational dimensions.

This repository currently has private visibility. Reviewers need access to
the repository or a supplied copy of this supplement to reproduce the checks.
