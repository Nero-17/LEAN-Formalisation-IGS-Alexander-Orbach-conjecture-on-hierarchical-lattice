# Paused Lean snapshot — 2026-10-10

The user paused formalisation and requested preservation of all existing Lean code.
The original Sections 2–4 package below is preserved. The newer independent
Section 3 project is included in **section3-continuation/**, with its pinned
dependencies, vendored sources, verification scripts and all working drafts.

**Section 3 remains incomplete.** Its last successful aggregate audit covers
5,646 declarations; the exact source hashes and scope are recorded in
section3-continuation/verification/manifest.json. Additional individually
compiled modules and unverified drafts are also preserved. A file being
present in this snapshot does not mean it compiled or belongs to the audit.
See section3-continuation/COVERAGE.md and PAUSED_SNAPSHOT.json.

To check the audited continuation closure, from section3-continuation/ run
`python scripts/verify.py --imported-only` after installing the pinned Lean
toolchain and fetching dependencies. This snapshot is a packaging operation;
it does not claim a fresh combined build or completed Section 3 proof.

---

# IGS: Alexander–Orbach conjecture on hierarchical lattices

This repository packages the existing Lean formalisation of Sections 2, 3 and 4
of IGS III. It contains Lean sources, pinned Lake dependencies and the required
third-party licence. The manuscript and research archives are separate.

## Build

Install [elan](https://github.com/leanprover/elan), then run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

Lean is pinned to **4.32.1** and mathlib to
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
The unified import is `IGSAlexanderOrbach`.
`Audit.lean` checks every packaged declaration, including private and generated
declarations, for transitive axioms other than `propext`, `Classical.choice`
and `Quot.sound`.

## Scope

| Directory | Status |
|---|---|
| `IGSIII/` | Completed Section 2 and its chemical-geometry Appendix A. |
| `IGSIII34/` | Existing verified Section 3 work and supporting dimension algebra. Section 3 remains in progress. |
| `IGSIII4/` | Completed Section 4, relative to explicitly listed Section 3 inputs. |
| `Universality/` | Required transitive IGS II Lean dependencies, included locally. |

Section 3 establishes actual finite-network electrical estimates, natural
resistance growth and its logarithmic limits, an endogenous positive field,
and physical L2 and all-address almost-sure amplitude convergence. Uniform
real moments and real-moment limits to fixed omega members are also proved.
Final all-order amplitude assembly, eigenlaw uniqueness, full resistance forms,
diffusion and actual heat-kernel spectral limits remain unfinished.

Section 4's accepted Section 3 facts are explicit theorem parameters in
`IGSIII4/AcceptedSectionThree.lean`. They are not new Lean axioms. Its completed
proofs do not establish the still-unfinished analytic inputs from Section 3.
The global Alexander–Orbach exclusion is a conjecture predicate, not a proved theorem.

Only formal modules that compiled in their original audited projects are included.
Uncompiled working drafts are kept outside this package.

The finite-dimensional Brouwer foundation is adapted from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838)
under the notice in `licenses/Harfe-MIT.txt`. Original copyright notices remain
in the corresponding Lean modules.
