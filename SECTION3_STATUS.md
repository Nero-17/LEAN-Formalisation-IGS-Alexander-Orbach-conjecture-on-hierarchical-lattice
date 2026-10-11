# Section 3: proved results and remaining scope

Updated October 11, 2026, Asia/Shanghai. The frozen Section3 scope is complete.
Section4 now instantiates its former accepted inputs with the actual proved
Section3 results. The repository default entry point is IGSAlexanderOrbach.

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

## Completed integration and exact scope

The original annealed marked-GHP/whole-path joint law, continuous-limit usual-local
J1 interpretation, exact physical measures and same-master original clocks are
complete within [Section3 coverage](COVERAGE.md). Its separate certificate audits
12,037 declarations and1,486 source hashes.

[Integrated Sections3–4 coverage](SECTION34_COVERAGE.md) and
[the actual Section4 proof index](SECTION34_RESULT_INDEX.md) identify the completed
adapters, original-model existence statements and actual typical heat-kernel
AO conclusions. The final integrated audit covers12,294 declarations and1,532
source hashes, including the six actual interface checks.

The global AO exclusion remains a conjecture. Continuous limiting representatives,
respective electrical/chemical marked-GHP topologies and physical-mass typical
compact-diffusion spectral scope are retained; no stronger statement is implied.
Historical publication/preservation manifests retain their original dated scope;
verification/section34/manifest.json is authoritative for the current unified package.
