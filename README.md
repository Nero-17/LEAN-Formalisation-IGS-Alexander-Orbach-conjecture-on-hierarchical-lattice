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

This repository packages the Lean formalisation of Sections 2, 3 and 4 of
IGS III. The root Lake package is the current verified entry point; it contains
Lean sources, pinned dependencies and the required third-party licence.
The manuscript and research archives are separate.

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

The October 11, 2026 continuation establishes the actual unique positive
mean-one natural electrical law, all-order amplitudes and real moments;
the compact electrical carrier, its identification with the chemical carrier,
the same full-support Perron probability mass, and the closed regular strongly
local resistance form. Whole original finite resolvents, the actual Feller
semigroup and positive conservative heat kernel, and the typical spectral
dimension formula are proved.

It also constructs the actual continuous limiting process and proves strong
Markov identities for its natural filtration at almost-surely finite stopping
times. Discrete, continuous rate-one and vertex-variable-speed original walks
have whole cadlag path-law convergence with their genuine natural clocks;
the exact deterministic-clock changes and common chemical isometric
realisations are included. These results are not obtained by assuming a
limiting process, a path-tightness conclusion or a spectral exponent.

**Section 3 is still marked in progress.** The whole-path topology currently
formalised uses genuine J1 time changes on every integer horizon. It is
stronger than the usual local J1 topology at paths with an integer-time jump.
At a continuous limit, uniform convergence on compact time intervals and
genuine J1 convergence on every real horizon are proved. The final usual-local
J1 weak-test bridge and the scalar speed-measure equivalence are being
completed; no equality of the two whole-path topologies is asserted.
See [the detailed scope and result index](SECTION3_STATUS.md).

Section 4's accepted Section 3 facts remain explicit theorem parameters in
`IGSIII4/AcceptedSectionThree.lean`. They are not new Lean axioms. The new
Section 3 work proves the natural electrical sandwich and mean upper bound,
and proves terminal-core pruning on every actual classical generation.
The final consolidated Section 4 adapter is separate from its existing proofs.
The global Alexander–Orbach exclusion is a conjecture predicate, not a proved theorem.

Only individually compiled formal modules are adopted by the unified root
package. Uncompiled working drafts are excluded from its import closure.
The publication manifest records the adopted sources and verification scope.

The finite-dimensional Brouwer foundation is adapted from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838)
under the notice in `licenses/Harfe-MIT.txt`. Original copyright notices remain
in the corresponding Lean modules.
