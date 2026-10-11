# IGS Bernoulli percolation and universality classes

Lean formalisation and reproducible supplementary material for
*Iterated Graph Systems (II): Bernoulli percolation and universality class on hierarchical lattices*.

The repository integrates Sections 2–5 in one dependency graph. Import
`Universality` for the complete development; `Audit.lean` checks every serialized
project-origin kernel declaration in that imported environment, including private
and generated declarations.

| Paper | Mathematical content | Entry or interface |
|---|---|---|
| Section 2 | Bernoulli substitution, finite-type mass recursions, spectral identities, recursive geometry | `Universality.Percolation`, `Universality.Matrix`, `Universality.Geometry` |
| Section 3 and appendix | Four physical exponents, three-dimension classification, noncommutative obstruction, conditional additional exponents | [Section3.lean](Universality/Section3.lean) |
| Section 4 | Algebraic growth factors, six-exponentials rank criterion, irreducibility and commensurability | [Section4Complete.lean](Universality/Arithmetic/Section4Complete.lean) |
| Section 5 | Actual graph certificates, infinite incommensurate family, transcendental example | [Section5.lean](Universality/Section5.lean) |

The shared objects are the same finite `Rule`, actual Bernoulli observables,
mass matrix and metric completion throughout. Section 4 consumes Section 3's
physical-class theorem; Section 5 realizes its examples as actual classical
rules and invokes that same theorem. See [coverage and interfaces](docs/COVERAGE.md).

The concrete almost-sure GH and graph-directed limit theorem for actual critical
percolation clusters is [Theorem 2.9](Universality/Geometry/PercolationTheorem29.lean).
It constructs the geometry from the rule and configurations, without assuming a
compatible geometric realisation.

## Verification

Use Lean **4.32.1** and the mathlib revision pinned in `lake-manifest.json`.
See [build instructions](docs/BUILD.md) for a fresh build, deterministic restoration
of large certificate data, and the scope of the published verification evidence.

The only external mathematical axioms are **Gelfond–Schneider** and the
**six exponentials theorem**. The four exponentials conjecture appears only as
an explicit hypothesis of conditional statements. See [logical dependencies](docs/DEPENDENCIES.md).

## Supplementary calculations

[Supplementary material](supplementary/README.md) contains exact input data,
integer verifiers, construction details and figures. Python calculations support
reproducibility; the claimed Lean results are proved in Lean.

The current tree contains the final mathematical sources and verification materials.
Development reports and intermediate execution logs are retained in Git history,
rather than in the reader-facing repository.
