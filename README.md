# IGS III Lean formalisation — active Section 3 continuation

Work resumed on October 11, 2026 to finish the actual annealed joint-law bridge and final audit. The latest Section 3 work is in
**[section3-continuation/](section3-continuation/)**, including compiled modules
and clearly identified working drafts. **Section 3 remains incomplete.** See [the handoff](section3-continuation/RESUME.md) for verified results and the remaining annealed joint-law bridge.

The root Lake package preserves the earlier verified Sections 2–4 baseline.
Its audit and the continuation audit have different scopes. For the current
continuation, consult [the result index](section3-continuation/SECTION3_RESULT_INDEX.md),
[coverage](section3-continuation/COVERAGE.md), and the exact source hashes in
[the latest successful audit](section3-continuation/verification/manifest.json).
A saved file or working draft is not certified merely by being present.
`PAUSED_SNAPSHOT.json` documents the earlier preservation snapshot, not the
current work status.

To reproduce the continuation audit, change to `section3-continuation/`, then run:

```sh
lake update
lake exe cache get
lake build Universality
python scripts/verify.py --imported-only
```

This is an incremental import-closure audit with pinned dependencies. The
recorded audit alone does not certify full manuscript coverage or a clean
rebuild of every saved draft.

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
