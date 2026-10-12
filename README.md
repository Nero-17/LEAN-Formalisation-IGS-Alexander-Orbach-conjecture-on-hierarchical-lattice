# IGS III Lean formalisation

This package formalises the reviewed results of **Iterated Graph Systems (III): Alexander–Orbach conjecture on hierarchical lattices**, including the actual critical-cluster spectral-density theorem and its supporting resistance moment estimates.

The English manuscript cutoff is `bfb73c0c34450dbb517261655cddda005b870d95` (12 October 2026), with raw `main.tex` SHA256 `cc53804aafbe60b25a644b829285ac558447ccafed538408a76f736fbf3efa60`. The private manuscript and its Chinese companion are not included. The Chinese companion is not a separately audited manuscript.

The default entry `IGSAlexanderOrbach.lean` imports `IGSIIILatestManuscript20261012.lean`. It includes the earlier actual-model geometry, mass, resistance, diffusion and typical heat-kernel proofs, the current vertex-mass/Perron/clock normalisation, and the new Appendix C construction. The old section-numbered modules retain their historical names after the manuscript's section split.

## New density result

For every nonempty open subinterval of `(1,2)`, the final theorem constructs an actual classical finite rule at its own interior critical probability whose natural diffusion has physical-mass typical spectral dimension in that interval. Its terminal distance, both terminal degrees, and terminal minimum edge cut are all exactly two.

The public entry is:

```lean
IGSIII4.SpectralDensity.ActualFamily.actual_physical_spectral_density_two_terminal_parameters20261012
```

Its only hypotheses concern the interval endpoints. The conclusion includes the physical mass measure and almost-everywhere diagonal heat-kernel exponent for the same natural resistance completion used in the growth estimates. No cell-moment, resistance-growth, transform, or target-density premise is supplied by the caller.

The proof derives the actual weighted circuit response, exact crossing-conditioned finite laws, a uniform normalised second-moment invariant, recursive generation bounds, natural resistance growth bounds, and full-cluster mass asymptotics. The finite-prefix `max length 2` patch preserves the classical graph conditions for every sequence entry.

**Global AO non-equality remains a conjecture.** Density near `4/3` neither constructs a finite rule attaining it nor excludes all such rules.

## Verification and scope

See [current manuscript correspondence](LATEST_MANUSCRIPT_COVERAGE.md), the [independent semantic verdict](verification/spectral-density20261012/semantic_review.json), and the [exact import-closure certificate](verification/spectral-density20261012/closure_manifest.json). The latter records every audited source and object hash, compiler-cache provenance, and every declaration enumerated by its originating module, including private and generated declarations. Allowed transitive axioms are only `propext`, `Classical.choice`, and `Quot.sound`.

Historical certificates in `verification/section234` and `verification/manuscript-sync20261012` retain their original cutoffs and scope; their old completion or in-progress labels are historical. Current manuscript changes after the original section certificate are covered by the supplemental correspondence and the new closure gate. In particular, the positive-`theta` and conditional-AO wording corrections are already present in the current manuscript.

The spectral result concerns the compact limiting natural diffusion, short time, and physical-mass typical points. It is not a blanket claim about every starting point or the long-time exponent on an infinite microscopic graph. Conditional localisation retains the joint law of both sides of the same failed socket.

## Build

Lean `4.32.1` and mathlib revision `520045ab14e26149ee970e2e617ca04b09bde5d6` are pinned.

```sh
lake exe cache get
lake build IGSAlexanderOrbach
python scripts/verify_latest_density.py --root . --output verification/local-density-check --required-module IGSIII4.SpectralDensity.ActualPhysicalDensity20261012 --interface IGSIII4.SpectralDensity.ActualFamily.actual_physical_spectral_density_two_terminal_parameters20261012
```

Keep the published dependency lockfile. The aggregate build compiles the required dependency modules; building every unimported vendor target is outside the certificate's scope. The portable verifier accepts an explicit package root, output directory, aggregate, and required interfaces. It can rebuild missing objects; exact matching historical compilation receipts may be reused. Mathematical statement correspondence remains a separate review from kernel and axiom checks.

`section3-continuation/` preserves earlier work and an updated copy of the imported sources; unimported drafts are outside the current theorem certificate. No PDF, manuscript TeX, or rendered figure is part of the repository.

The finite-dimensional Brouwer foundation is adapted from [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838) under `licenses/Harfe-MIT.txt`. Existing IGS-RWDL provenance is retained.
