# Section 3: proved results and remaining scope

Updated October 11, 2026, Asia/Shanghai. This is a publication of existing
proved results, not a claim that the entire manuscript has been formalised.
Section 2 and Section 4 sources are preserved.

## Result index

| Result | Main entry modules |
|---|---|
| Unique positive natural electrical law and all real moments | [NaturalResistance](IGSIII34/Percolation/Continuation/NaturalResistanceCompletion20261011.lean), [NaturalPhysicalOmega](IGSIII34/Percolation/Continuation/NaturalPhysicalOmegaCompletion20261011.lean) |
| Full compact resistance form, regularity, strong locality and recurrence criterion | [ActualRegularity](IGSIII34/Forms/ActualRegularityCompletion20261011.lean), [ActualLocality](IGSIII34/Forms/ActualLocalityCompletion20261011.lean), [L2Closedness](IGSIII34/Forms/L2ClosednessCompletion20261011.lean), [ActualFormRecurrence](IGSIII34/Forms/ActualFormRecurrenceCompletion20261011.lean) |
| Original whole finite resolvents, on the same actual Perron mass | [ActualNaturalResolventWitness](IGSIII34/Diffusion/ActualNaturalResolventWitnessCompletion20261011.lean) |
| Actual Feller semigroup, transition kernel and heat kernel | [ActualSpectralData](IGSIII34/Spectral/ActualSpectralDataCompletion20261011.lean), [ActualTransitionKernel](IGSIII34/Spectral/ActualTransitionKernelCompletion20261011.lean), [ActualFellerSemigroup](IGSIII34/Spectral/ActualFellerSemigroupCompletion20261011.lean) |
| Actual typical-point spectral dimension, with the mass and spectral data constructed internally | [ActualNaturalTypicalSpectral](IGSIII34/Spectral/ActualNaturalTypicalSpectralCompletion20261011.lean) |
| Original discrete walks: whole cadlag laws and same-mass spectral witness | [ActualNaturalDiscreteCadlagWitness](IGSIII34/Diffusion/ActualNaturalDiscreteCadlagWitnessCompletion20261011.lean) |
| Original rate-one continuous walks: whole cadlag laws and same-mass spectral witness | [ActualNaturalContinuousCadlagWitness](IGSIII34/Diffusion/ActualNaturalContinuousCadlagWitnessCompletion20261011.lean) |
| Original vertex-variable-speed walks: whole cadlag laws and same-mass spectral witness | [ActualClassicalVertexSpeedCadlagWitness](IGSIII34/Diffusion/ActualClassicalVertexSpeedCadlagWitnessCompletion20261011.lean) |
| Natural filtration and almost-surely finite stopping-time strong Markov law | [ActualNaturalMarkov](IGSIII34/Diffusion/ActualNaturalMarkovCompletion20261011.lean), [ActualStrongMarkovKernelLaw](IGSIII34/Diffusion/ActualStrongMarkovKernelLawCompletion20261011.lean) |
| Same chemical/electrical carrier and exact finite birth diagram | [ActualCarrierHomeomorphBirth](IGSIII34/ResistanceLimit/ActualCarrierHomeomorphBirthCompletion20261011.lean) |
| A single compact complete ambient space with true finite chemical isometries | [ActualChemicalCommonRealisation](IGSIII34/ResistanceLimit/ActualChemicalCommonRealisationCompletion20261011.lean), [ActualCommonChemicalCadlagWholeWeak](IGSIII34/Diffusion/ActualCommonChemicalCadlagWholeWeakCompletion20261011.lean) |
| Exact paper deterministic clocks and their positive random limiting time changes | [ActualClassicalPaperDeterministicWitness](IGSIII34/Diffusion/ActualClassicalPaperDeterministicWitnessCompletion20261011.lean) |
| Terminal-core pruning preserves the actual finite resistance | [ActualTerminalCorePruning](IGSIII34/Resistance/ActualTerminalCorePruningCompletion20261011.lean) |

The typical spectral dimension is
`2 * log(rho) / (log(rho) + log(natural resistance growth))`.
Its proof uses real diagonal-resolvent bounds and a proved Tauberian argument,
not an assumed heat-kernel exponent. Physical electrical amplitudes are retained.

The natural discrete/rate-one clock is `2 |E| growth^(depth+1)`.
The vertex-variable-speed clock is `|V| growth^(depth+1)` and its genuine
holding times are `Exp(1)/degree`. The deterministic algebraic clock is
`(rho * growth)^(depth+1)`; its limit has the proved random scalar time factor.
Lean depth zero denotes the first generator; paper generation zero denotes
one edge. The shift by one is therefore intentional.

## Remaining scope

- Whole cadlag convergence is proved in the topology formed from genuine J1
  metrics on every integer horizon. Its continuous-limit, arbitrary real
  horizon bridge is proved. The independent usual-local J1 weak-test wrapper
  remains to be integrated; the two global topologies are not called equal.
- The scalar time changes are actual path-law conclusions. The manuscript's
  equivalent scalar speed-measure form/kernel interpretation is still being
  consolidated.
- Original common chemical ambient results use the already formalised
  Section 2 length/mesh interfaces. Final outer witnesses and the Section 4
  dependency adapter are still being consolidated.
- Analytic resistance-form recurrence and a positive integrable semigroup
  occupation criterion are distinguished from a theorem about repeated
  sample-path hitting of every open set.
- The global Alexander–Orbach non-equality remains the manuscript conjecture.

## Verification and historical material

The unified entry point is `IGSAlexanderOrbach`. `Audit.lean` checks every
module-origin declaration in all four local namespaces, including private and
generated declarations, and recursively permits only `propext`,
`Classical.choice` and `Quot.sound`.
The [publication manifest](verification/section3-source-manifest.json) records
exact source hashes and the verification that actually ran. A cached-object
unified audit is distinguished from a fresh clean Lake rebuild.

This publication passed the unified Section 3 import, the complete package
entry, and the all-namespace transitive axiom audit for **13,485 declarations**.
All 1,547 adopted local module source hashes were rechecked after the audit.
Only the three standard Lean axioms were found. A fresh clean Lake rebuild
was not run for this snapshot; the full-manuscript completion flag remains false.

The existing `section3-continuation/` directory and `PAUSED_SNAPSHOT.json` are
the earlier user-requested pause snapshot. They are preserved for provenance
and are not the current unified proof entry point. Their historical status
files may describe earlier unfinished work. No manuscript PDF or TeX source
is added by this publication.
