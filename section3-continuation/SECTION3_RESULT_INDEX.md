# Section 3 proof index

Source manuscript: `db2cbd8163ef90cc70ebd4d97f282993fd3311b6`.
Status: integration in progress. Consult `COVERAGE.md` and the exact hashes in
`verification/manifest.json`; this index is not a verification certificate.

| Manuscript obligation | Formal entry point |
|---|---|
| Actual natural electrical multiplier, amplitudes, all-order convergence and eigenlaw uniqueness | `Percolation/Continuation/NaturalResistanceCompletion20261011.lean`, `exists_natural_resistance_completion20261011` |
| All logarithmic exponents for that same multiplier | `Percolation/Continuation/NaturalResistanceExponents.lean`, `natural_resistance_exponents` |
| Electrical/chemical growth and amplitude bounds | `Diffusion/NaturalResistanceChemicalComparison.lean`, `Diffusion/NaturalResistanceAmplitudeBounds.lean` |
| Actual full finite trace form and uniqueness | `ResistanceLimit/ActualTraceMinimum.lean`, `ActualTraceUniqueness.lean`, `ActualCompletionTraceUniqueness.lean` |
| Variational resistance for arbitrary completion points | `ResistanceLimit/ActualCompletionResistance.lean`, `actual_completion_variational_resistance_eq` |
| Same chemical/electrical carrier, physical mass, both marked GHP limits, original natural and deterministic clocks, limiting process and typical heat-kernel exponent | `Spectral/Collars/ActualSameMasterAllClocks.lean`, `exists_ae_actual_natural_common_section_three_all_clocks` |
| Genuine usual-local J1 probability-law convergence | `Diffusion/UsualLocalJ1PathLaw.lean`, `UsualLocalJ1ContinuousLimitRecovery.lean` and the actual master above |
| Exact completed-form retained-component energy decomposition | `Forms/ActualCompletedComponentEnergy.lean`, `ae_actual_natural_completed_component_energy_decomposition` |
| Intrinsic local resistance inequality | `Diffusion/ActualElectricalComponentCompletion.lean` |
| Completed finite-energy zero extension with exact local restriction and energy scaling | `Diffusion/ActualElectricalComponentZeroExtension.lean` |
| Actual selecting-configuration / complete trace-code root law, including the two dependent B sides | `ResistanceLimit/ElectricalSelectedRootLaw.lean`, `ElectricalComponentRootLaw.lean` |
| Required fivefold subdivided diamond example | `Spectral/Collars/FivefoldDiamondGraph.lean`, `FivefoldDiamondResistance.lean`, `FivefoldDiamondSpectralBound.lean` (actual critical witness and strict bound compiled) |
| Section 4's electrical interface from the actual natural witness | `Percolation/Continuation/SectionFourDependency.lean`, `exists_actual_section_four_electrical` |

All paths in this table are relative to `IGSIII34/`. Canonical closed-component
identification, exact intrinsic/global energy correspondence and explicit support
of zero extension are compiled in the ResistanceLimit actual component leaves.
The remaining annealed joint-law coding/measurability obligation is tracked in `COVERAGE.md`.

The process conclusions concern the compact limiting diffusion and typical
points, with original finite clocks and generation shifts retained. They do
not assert an infinite microscopic graph's long-time return exponent or a
spectral exponent at every finite-born vertex. The generic discontinuous-limit
metrization of the local path topology is not claimed; continuous-limit
neighborhood recovery covers the actual diffusion limits. The auxiliary
Appendix B resolvent identity is currently certified for parameter at least
one, the range needed for the small-time spectral theorem.

No global Alexander–Orbach exclusion theorem is claimed.
