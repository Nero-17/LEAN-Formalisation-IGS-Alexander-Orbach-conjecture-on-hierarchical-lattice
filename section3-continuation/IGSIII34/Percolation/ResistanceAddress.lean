import IGSIII34.Percolation.ResistanceExponent

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork IGSIII34.Probability Filter
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped _root_.Topology NNReal ENNReal

theorem electricalIteration_integral_at_address
    (rule : Rule) (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (address : List (Fin rule.edges))
    (response : ℝ → ℝ) (responseMeasurable : Measurable response) :
    (∫ marks, response (electricalIteration rule marks depth address)
      ∂independentInnovationLaw rule parameter positive belowOne fixedPoint) =
      ∫ marks, response (electricalIteration rule marks depth [])
        ∂independentInnovationLaw rule parameter positive belowOne fixedPoint := by
  have mapped := integral_map (μ := independentInnovationLaw rule parameter positive belowOne fixedPoint)
    (φ := innovationTreeShift rule address)
    (f := fun marks => response (electricalIteration rule marks depth []))
    (innovationTreeShift_measurable rule address).aemeasurable
    (responseMeasurable.comp (electricalIteration_measurable rule depth [])).aestronglyMeasurable
  rw [(innovationTreeShift_preserving rule parameter positive belowOne fixedPoint address).map_eq] at mapped
  simpa only [electricalIteration_shift, List.append_nil] using mapped.symm

theorem electricalIteration_log_limit_at_all_addresses
    (rule : Rule) (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (growth : ℝ)
    (rootLimit : ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      Tendsto (fun depth : ℕ => Real.log (electricalIteration rule marks depth [])/depth) atTop (𝓝 (Real.log growth))) :
    ∀ᵐ marks ∂independentInnovationLaw rule parameter positive belowOne fixedPoint,
      ∀ address : List (Fin rule.edges),
        Tendsto (fun depth : ℕ => Real.log (electricalIteration rule marks depth address)/depth) atTop (𝓝 (Real.log growth)) := by
  apply ae_all_iff.mpr
  intro address
  have shifted := (innovationTreeShift_preserving rule parameter positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootLimit
  simpa only [electricalIteration_shift, List.append_nil] using shifted

end
end IGSIII34.Percolation
