import IGSIII34.Percolation.ElectricalTransfer

set_option autoImplicit false

namespace IGSIII4
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability IGSIII34.Percolation

theorem electricalTransfer_congr_ae (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (same : first =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint] second) :
    electricalTransfer rule first =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
      electricalTransfer rule second := by
  have children : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      ∀ edge, first (innovationTreeShift rule [edge] marks) = second (innovationTreeShift rule [edge] marks) := by
    rw [ae_all_iff]
    intro edge
    exact (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae same
  filter_upwards [children] with marks equality
  exact congrArg (electricalCell rule.network (marks ([], true))) (funext equality)

theorem electricalTransfer_scale_ae (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    {value : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (nonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ value marks)
    {scalar : ℝ} (scalarNonnegative : 0 ≤ scalar) :
    electricalTransfer rule (fun marks => scalar * value marks)
      =ᵐ[independentInnovationLaw rule probability positive belowOne fixedPoint]
        fun marks => scalar * electricalTransfer rule value marks := by
  have children : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      ∀ edge, 0 ≤ value (innovationTreeShift rule [edge] marks) := by
    rw [ae_all_iff]
    intro edge
    exact (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae nonnegative
  filter_upwards [children] with marks bounds
  exact electricalCell_scale rule.network (marks ([], true)) bounds scalarNonnegative

theorem electricalTransfer_superadditive_ae (rule : Rule) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (fixedPoint : rule.network.reliability probability = probability)
    {first second : ((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ}
    (firstNonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ first marks)
    (secondNonnegative : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint, 0 ≤ second marks) :
    ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      electricalTransfer rule first marks + electricalTransfer rule second marks ≤
        electricalTransfer rule (fun marks => first marks + second marks) marks := by
  have firstChildren : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      ∀ edge, 0 ≤ first (innovationTreeShift rule [edge] marks) := by
    rw [ae_all_iff]
    intro edge
    exact (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae firstNonnegative
  have secondChildren : ∀ᵐ marks ∂independentInnovationLaw rule probability positive belowOne fixedPoint,
      ∀ edge, 0 ≤ second (innovationTreeShift rule [edge] marks) := by
    rw [ae_all_iff]
    intro edge
    exact (innovationTreeShift_preserving rule probability positive belowOne fixedPoint [edge]).quasiMeasurePreserving.ae secondNonnegative
  filter_upwards [firstChildren, secondChildren] with marks firstBounds secondBounds
  exact electricalCell_superadditive rule.network (marks ([], true)) firstBounds secondBounds

end
end IGSIII4
