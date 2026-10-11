# IGS III Lean formalisation

**The repository root now builds the integrated Sections3–4 package.**
The default entry point is `IGSAlexanderOrbach.lean`, importing the completed
Section3 and the actual Section4 adapters. The original-model existence results
construct the natural electrical field, mean sandwich, pruning and typical
heat-kernel limit from proved Section3 results. No formerly accepted Section3
certificate or arbitrary supplied spectral formula is an input to those final
model-only theorems.

The final audit covers 12,294 declarations and
1,532 exact source hashes. It checks all transitive axioms,
including private/generated constants, and the six actual interface signatures.
Only `propext`, `Classical.choice` and `Quot.sound` are allowed.
The frozen manuscript commit is
`db2cbd8163ef90cc70ebd4d97f282993fd3311b6`.

See [integrated coverage](SECTION34_COVERAGE.md),
[the Section4 proof index](SECTION34_RESULT_INDEX.md),
[the integrated certificate](verification/section34/manifest.json),
and [the reviewed correspondence](verification/section34/section4_correspondence.json).
The completed Section3 retains its separate
[coverage](COVERAGE.md) and [certificate](verification/manifest.json).

```sh
lake update
lake exe cache get
lake build Universality
python scripts/verify_integrated_sections.py --imported-only --complete
```

Lean4.32.1 and mathlib
`520045ab14e26149ee970e2e617ca04b09bde5d6` are pinned.
The certificate checks the full dependency closure, reusing only exact matching
previous source/object hashes. It does not claim a clean rebuild of every saved
draft. `section3-continuation/` also preserves saved working files outside that
closure, distinguished in its snapshot.

The spectral conclusion concerns the compact limiting diffusion, small time and
physical-mass typical points. The AO exclusion outside the stated open rectangle
and the fivefold subdivided diamond example are proved. The global AO exclusion
remains a conjecture; no result for every rule in the remaining rectangle is
claimed. Section3's continuous-limit usual-local J1 and respective electrical/
chemical marked-GHP scope are retained.

The finite-dimensional Brouwer foundation is adapted from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838)
under `licenses/Harfe-MIT.txt`. The authorised IGS-RWDL source/provenance remains
in `section3-continuation/third-party/IGS-RWDL/`. The private manuscript and full
research archives are stored separately from this public code repository.
