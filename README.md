# IGS III Lean formalisation

## Latest manuscript update (12 October 2026): in progress

The manuscript has advanced to `551b8a5` and adds a spectral-density theorem.
The new [synchronisation status](verification/manuscript-sync20261012/STATUS.md)
and [exact-source receipts](verification/manuscript-sync20261012/manifest.json)
cover the saved new proofs. The density theorem is **not yet proved in Lean**.
Build the partial new entry with `lake build IGSIIILatestManuscript20261012`.
The default entry and completion numbers below describe the earlier certified
manuscript72298e5, not the new source. Its proposed theta/AO wording corrections
have since been applied in Overleaf and are present in the newer source.

The default `IGSAlexanderOrbach.lean` imports the latest reviewed Sections2–5
through the retained aggregate name `IGSIIISectionsTwoThreeFour.lean`.
The original Sections2–4 task topics now occupy Sections2–5 after the diffusion/AO
section split. The private Overleaf source audited
here is commit `72298e5c47d6f5451dd8ed2e91d0b82dcd3777a3`.

The latest correspondence records 60 environments with 61 labels, 75 obligations and 273
exact Lean entry mappings, including the separate AO equivalence. Final actual
constructors produce their electrical field, geometry, mass, resistance form,
process and typical spectral dimension from the stated model hypotheses.
Former accepted Section3 target certificates are discharged by actual proofs.

The current supporting resolvent identities and component bound cover every
positive parameter. The literal variational supremum over nonzero functions is
proved in `PositiveResolventNonzeroSupremum20261011.lean`.

**Necessary source corrections:** AppendixA's chemical-paths exponential
estimates must explicitly require `theta > 0`. The literal unrestricted-sign
statement is false. Lean retains the correct sign; the certificate accordingly
sets `literalUncorrectedManuscriptComplete` to false and records the correction.
The latest AO-region statement also dropped its spectral-dimension conditional.
Its proof and the introduction establish: AO equality forces the dimension pair
inside the rectangle, so equality is excluded outside it. They do not prove that
every rule lies outside the rectangle. The correspondence certifies the restored
conditional result and explicitly rejects the literal stronger statement.
The global conjecture remains unproved and concerns the natural diffusion at
physical-mass typical points. A private proposed patch records these corrections;
the Overleaf project itself has not been changed by this audit.

Cell-localisation independence refers to connected cells at distinct socket
addresses, conditional on ancestor raw innovations. The two sides of one B
socket retain their joint law. Conditioning on descendant-dependent limiting
lengths is not covered by that independence statement.

The fresh certificate audits 12,483 imported project
declarations across 1,554 exact source files. Transitive private/generated
constants are included; only `propext`, `Classical.choice` and `Quot.sound` are
allowed. Exact unchanged source/object pairs may be reused during compilation;
this is not a clean rebuild of every saved draft. Historical certificates retain
their historical scope and are not the current completion basis.

See [latest coverage](SECTION234_COVERAGE.md),
[latest proof index](SECTION234_RESULT_INDEX.md),
[fresh certificate](verification/section234/manifest.json), and
[reviewed correspondence](verification/section234/latest_correspondence.json).

```sh
lake update
lake exe cache get
lake build Universality
python scripts/verify_latest_sections.py --imported-only --complete
```

Lean4.32.1 and mathlib `520045ab14e26149ee970e2e617ca04b09bde5d6` are pinned.
The optional private `paper/latest-main.tex` is checked against its recorded
hash when locally present; it is excluded from this public repository.
`section3-continuation/` preserves saved work outside the aggregate closure,
with exact scope distinguished in its progress snapshot.

The spectral result concerns the compact limiting diffusion, small time and
physical-mass typical points. The all-start quenched and annealed conclusions
retain their stated marked-GHP and continuous-limit usual-local J1 scope.
Section5's exclusion of AO equality outside the stated open rectangle and its fivefold diamond
example are proved; the global AO exclusion remains a conjecture.

The finite-dimensional Brouwer foundation is adapted from
[harfe/fixed-point-theorems-lean4](https://github.com/harfe/fixed-point-theorems-lean4/tree/770940ddf9878cf61952ed53d910b92bca841838)
under `licenses/Harfe-MIT.txt`. IGS-RWDL provenance is preserved in the saved
continuation. Private manuscripts and full round archives are stored separately.
