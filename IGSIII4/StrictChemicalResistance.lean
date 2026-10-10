import IGSIII4.CriticalSupersolution
import IGSIII4.ElectricalChemicalComparison
import IGSIII4.InnovationRootAtom

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability IGSIII34.Percolation

theorem strict_chemical_resistance_of_eigenfunction (rule : Rule) (classicalRule : rule.Classical)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    (accepted : AcceptedElectricalSectionThree rule probability positive belowOne fixedPoint)
    (value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ)
    (measurable : Measurable value)
    (integrable : Integrable value (independentInnovationLaw rule probability positive belowOne fixedPoint))
    (valuePositive : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 < value marks)
    (meanPositive : 0 < ∫ marks, value marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint)
    {chemicalGrowth : ℝ} (chemicalGrowthPositive : 0 < chemicalGrowth)
    (chemicalEquation : chemicalTransfer rule value
      =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
        fun marks => chemicalGrowth * value marks) :
    1 < accepted.growth ∧ accepted.growth < chemicalGrowth := by
  have childrenPositive : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      ∀ edge, 0 < value (innovationTreeShift rule [edge] marks) := by
    apply ae_all_iff.mpr
    intro edge
    exact (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae valuePositive
  have nonnegative := valuePositive.mono (fun _ above => above.le)
  have supersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ chemicalGrowth * value marks := by
    filter_upwards [childrenPositive, chemicalEquation,
      independentInnovationLaw_crosses rule probability positive belowOne fixedPoint] with marks childPositive equation crossing
    calc
      _ ≤ chemicalTransfer rule value marks := electricalCell_le_shortest rule.network classicalRule.simple
        (marks ([], true)) (crossing [] true) _ (fun edge => (childPositive edge).le)
      _ = _ := equation
  have lower := supersolution_growth_lower_bound rule classicalRule probability positive belowOne fixedPoint accepted
    value measurable integrable nonnegative meanPositive chemicalGrowthPositive supersolution
  refine ⟨accepted.growthAboveOne, lt_of_le_of_ne lower ?_⟩
  intro equality
  have criticalSupersolution : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule value marks ≤ accepted.growth * value marks := by
    simpa only [equality] using supersolution
  obtain ⟨scalar, scalarPositive, same⟩ := critical_supersolution_rigidity rule classicalRule probability positive belowOne
    fixedPoint accepted value measurable integrable nonnegative meanPositive criticalSupersolution
  have transferSame := electricalTransfer_congr_ae rule probability positive belowOne fixedPoint same
  have transferScaling := electricalTransfer_scale_ae rule probability positive belowOne fixedPoint
    (accepted.fieldPositive.mono (fun _ above => above.le)) scalarPositive.le
  have electricalEquation : electricalTransfer rule value
      =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
        fun marks => chemicalGrowth * value marks := by
    filter_upwards [same, transferSame, transferScaling, accepted.fieldEquation]
      with marks identity transferIdentity scaling eigenvalue
    rw [transferIdentity, scaling, eigenvalue, identity, ← equality]
    ring
  have agreement : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      (∀ edge, 0 < value (innovationTreeShift rule [edge] marks)) ∧
        electricalTransfer rule value marks = chemicalTransfer rule value marks := by
    filter_upwards [childrenPositive, electricalEquation, chemicalEquation] with marks childPositive electrical chemical
    exact ⟨childPositive, electrical.trans chemical.symm⟩
  have eventPositive := innovation_root_atom_positive rule probability positive belowOne fixedPoint (fun _ => true)
    ((rule.network.crosses_eq_true _).mpr (classicalRule.connected _))
  obtain ⟨marks, allOpen, childPositive, agrees⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae
    eventPositive.ne' (ae_restrict_of_ae agreement)
  have strict := classical_allOpen_resistance_lt_shortest rule classicalRule
    (fun edge => value (innovationTreeShift rule [edge] marks)) childPositive
  change marks ([], true) = (fun _ => true) at allOpen
  change electricalCell rule.network (marks ([], true)) _ =
    (edgePathFamily rule.network (marks ([], true))).shortest _ at agrees
  rw [allOpen] at agrees
  exact (ne_of_lt strict) agrees

end
end IGSIII4
