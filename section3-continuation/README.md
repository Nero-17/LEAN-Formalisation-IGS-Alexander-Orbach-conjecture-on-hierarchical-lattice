# Section 3 formalisation

The manuscript obligations for frozen source commit
`db2cbd8163ef90cc70ebd4d97f282993fd3311b6` are complete within the explicit
scope in `COVERAGE.md`. The original chemical metric, ordered marks, both
physical masses and whole-path law occur in one genuine joint probability law;
the usual-local J1 interpretation is proved at the continuous diffusion limits.
Electrical marked GHP is also proved on the same environmental event.

The final aggregate audit covers 12,037 declarations
and permits only `propext`, `Classical.choice` and `Quot.sound`.
`verification/section3_correspondence.json` links the reviewed manuscript
obligations to audited declarations and exact source hashes. The audit is an
incremental source/object check, not a claim of a clean rebuild.

This directory also preserves working drafts outside the audited import
closure. `PROGRESS_SNAPSHOT.json` distinguishes them by exact hashes.
The repository root retains the earlier baseline; this continuation directory
contains the completed Section 3 package. No global AO exclusion theorem,
simultaneous two-metric joint topology or generic discontinuous-limit local-J1
metrization is claimed.

With the pinned Lean and mathlib dependencies installed, reproduce the final
certificate from this directory with
`python scripts/verify.py --imported-only --section3-complete`.
