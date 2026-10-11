# Section4 actual-proof integration index

Frozen manuscriptcommitdb2cbd8163ef90cc70ebd4d97f282993fd3311b6.
Completion requires the final verification/section34/manifest.json certificate.

| Obligation | Actual formal entry points |
|---|---|
| Former electrical field and lower sandwich inputs discharged (main.tex539–620;1161–1264) | [naturalSectionFourElectrical](IGSIII34/Percolation/Continuation/SectionFourDependency.lean)<br>[exists_section_four_from_proved_sections_two_three](IGSIII4/ActualSectionFour.lean) |
| Former mean-upper and terminal-core pruning inputs discharged (main.tex574–620;1252–1264) | [naturalSectionFourMeanUpper](IGSIII4/ActualSectionThreeInputs.lean)<br>[natural_electrical_mean_upper_completion20261011](IGSIII34/Percolation/Continuation/NaturalMeanUpperCompletion20261011.lean)<br>[actual_section_four_core_pruning](IGSIII4/ActualSectionThreeInputs.lean)<br>[classical_actual_core_pruning_section_three_completion20261011](IGSIII34/Resistance/ActualTerminalCorePruningCompletion20261011.lean) |
| Critical supersolution growth and equality rigidity (main.tex1183–1218) | [natural_critical_supersolution](IGSIII4/ActualSectionFour.lean) |
| Strict chemical/electrical multiplier comparison (main.tex1220–1233) | [section_four_for_natural_resistance](IGSIII4/ActualSectionFour.lean)<br>[actual_strict_chemical_resistance](IGSIII4/ActualChemicalData.lean) |
| Full mass/core growth and strict clock/dimension comparison (main.tex1235–1265) | [section_four_for_natural_resistance](IGSIII4/ActualSectionFour.lean)<br>[terminalCoreMean_strictly_below_mass_radius](IGSIII4/TerminalCore.lean)<br>[actual_core_growth_clock](IGSIII4/ActualCoreClock.lean)<br>[actual_dimension_comparisons](IGSIII4/AlexanderOrbach.lean) |
| AO mass and dimension equalities for the actual spectral limit (main.tex1162–1181;1275–1283) | [exists_ae_actual_section_four_typical_heat_kernel](IGSIII4/ActualTypicalPointSectionFour.lean)<br>[section_four_for_natural_resistance](IGSIII4/ActualSectionFour.lean) |
| AO exclusion outside the open rectangle, including boundaries (main.tex1267–1284) | [exists_actual_section_four_and_typical_heat_kernel](IGSIII4/ActualTypicalPointSectionFour.lean)<br>[actual_ao_region](IGSIII4/AlexanderOrbach.lean) |
| Strict spectral sign in both stated mass regions (main.tex1286–1289) | [exists_ae_actual_section_four_typical_heat_kernel](IGSIII4/ActualTypicalPointSectionFour.lean) |
| Fivefold subdivided diamond at its own critical point (main.tex1291–1300) | [natural_long_diamond_spectral_dimension_strictly_below_four_thirds](IGSIII4/ActualSectionFour.lean)<br>[actual_chemical_factor_ten](IGSIII4/LongDiamond.lean)<br>[chemical_mass_dimension_bound](IGSIII4/LongDiamond.lean) |
| Actual typical-point formula constructed, with outer and inner AE measures (main.tex1077–1157;1162–1300) | [exists_actual_section_four_and_typical_heat_kernel](IGSIII4/ActualTypicalPointSectionFour.lean)<br>[exists_ae_actual_natural_typical_spectral_completion20261011](IGSIII34/Spectral/ActualNaturalTypicalSpectralCompletion20261011.lean) |

Scope:

- The final two existence entrypoints take precisely six original-model parameters and construct natural/chemical/geometry/mass/spectral witnesses.
- Historical Accepted* structures are data certificates for general helper lemmas, not axioms or inputs of final actual results.
- The typical spectral assertion is the actual compact diffusion diagonal logarithmic small-time limit, under original innovation AE and physical-mass AE.
- Dimension quantities use the established logarithmic mass/chemical/resistance growth formulas; the earlier geometry identification remains in the completed Section3 scope.
- The complete imported project closure is compiled/checked against exact source/object hashes; unimported saved drafts and a clean rebuild of all drafts are not claimed.
- No global AO exclusion is proved. NaturalGlobalAlexanderOrbachConjecture is a predicate only.
- Section3 continuous-limit usual-local J1, respective chemical/electrical marked GHP and typical compact-diffusion scope are preserved.
