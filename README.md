# IGS III Lean formalisation

**The completed Section 3 package is in [section3-continuation/](section3-continuation/).**
It formalises the obligations of frozen manuscript commit
`db2cbd8163ef90cc70ebd4d97f282993fd3311b6`, including the actual original
annealed marked-GHP/whole-path convergence and the continuous-limit usual-local
J1 interpretation. The final aggregate audit covers
12,037 declarations and permits only
`propext`, `Classical.choice` and `Quot.sound`.

See [coverage](section3-continuation/COVERAGE.md),
[the manuscript proof index](section3-continuation/SECTION3_RESULT_INDEX.md),
[the exact audit manifest](section3-continuation/verification/manifest.json),
and [the reviewed correspondence](section3-continuation/verification/section3_correspondence.json).
Saved unimported drafts are distinguished by exact hashes in
`section3-continuation/PROGRESS_SNAPSHOT.json` and are outside the certificate.

The certified results include the actual natural electrical eigenlaw,
amplitudes and uniqueness; the regular strongly local full resistance form;
the common chemical/electrical carrier and physical mass; the original natural
and deterministic clocks; genuine annealed joint limits; typical compact-diffusion
spectral dimension; and the fivefold subdivided diamond strict non-AO example.
No global Alexander–Orbach exclusion theorem is claimed. Electrical marked GHP
is proved in its respective topology on the same physical master; no stronger
simultaneous two-metric-and-path joint topology is asserted.

To reproduce the completed continuation certificate:

```sh
cd section3-continuation
lake update
lake exe cache get
lake build Universality
python scripts/verify.py --imported-only --section3-complete
```

Lean is pinned to4.32.1 and mathlib to
`520045ab14e26149ee970e2e617ca04b09bde5d6`.
The recorded certificate is an incremental source/object audit; it is not a
claim that every saved draft underwent a clean rebuild.

The repository root retains the earlier Sections2–4 baseline and its separate
`IGSAlexanderOrbach` entry point. Section4 remains relative to its explicitly
listed Section3 inputs. The current completed Section3 entry point is
`section3-continuation/IGSIII34.lean`; use its certificate for the new results.
The manuscript and full research archives remain separate from this code repository.

The finite-dimensional Brouwer foundation is adapted from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838)
under `licenses/Harfe-MIT.txt`, with original notices retained in the Lean modules.
The user-authorised IGS-RWDL reuse is pinned to
`7f93c64184dcbfa7a1c35080cde713933104deab`; its Apache-2.0 licence and provenance
remain in `section3-continuation/third-party/IGS-RWDL/`.
