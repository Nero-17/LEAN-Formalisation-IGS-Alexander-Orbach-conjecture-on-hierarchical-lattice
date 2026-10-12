# Alexander–Orbach conjecture on hierarchical lattices

Lean formalisation of *Iterated Graph Systems (III): Alexander–Orbach conjecture on hierarchical lattices*.

The development covers chemical geometry and mass, natural resistance, diffusion, typical-point spectral dimension, Alexander–Orbach exclusion criteria, and density of spectral dimensions in `(1, 2)` for classical hierarchical lattices at their own critical percolation probabilities. The assertion that no classical hierarchical lattice attains spectral dimension `4/3` remains a conjecture.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
```

The toolchain and dependency lockfile pin Lean `4.32.1` and the required mathlib version.

## Use

```lean
import IGSAlexanderOrbach
```

| Directory | Content |
|---|---|
| [`IGSIII/`](IGSIII) | Chemical geometry, branching structure and cluster mass |
| [`IGSIII34/`](IGSIII34) | Resistance, diffusion and heat kernels |
| [`IGSIII4/`](IGSIII4) | Alexander–Orbach criteria and spectral-dimension density |
| [`vendor/Universality/`](vendor/Universality) | Shared graph and percolation foundations |

Spectral dimension refers to the small-time heat-kernel exponent of the natural limiting diffusion at physical-mass-almost-everywhere points.

## Attribution

The Brouwer fixed-point foundation incorporates work from [harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838), under the [MIT licence](licenses/Harfe-MIT.txt). The IGS-RWDL foundation is distributed under the [Apache 2.0 licence](licenses/IGS-RWDL-Apache-2.0.txt).
