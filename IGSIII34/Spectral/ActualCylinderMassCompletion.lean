import IGSIII34.Spectral.ActualMassMaximaCompletion
import IGSIII.Mass.ComponentCylinderWeights
import IGSIII34.Diffusion.ComponentEdgeLimits

/-! The same actual Section 2 component probability weights satisfy
all-address subexponential mass upper bounds relative to the critical
Perron growth. No probability measure or mass field is an input. -/
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution
open MeasureTheory Filter Matrix
open scoped Topology

theorem exists_actual_component_weight_subexponential_upper
    {rule : Rule} (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ weight : List (Fin rule.edges × Bool) →
        (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ),
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        weight [] marks = 1 ∧
        (∀ address, 0 ≤ weight address marks ∧
          weight address marks = ∑ choice : Fin rule.edges × Bool, weight (address ++ [choice]) marks ∧
          Tendsto (fun depth => markedOrientedVertexMass rule marks depth (componentEdgeAddress address)
            (retainedComponentState rule marks address) /
              markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
            atTop (𝓝 (weight address marks)) ∧
          (retainedComponentState rule marks address = .inactive → weight address marks = 0) ∧
          (retainedComponentState rule marks address = .connected → 0 < weight address marks)) ∧
        ∀ growth : ℝ, 1 < growth → ∃ bound : ℝ, 0 < bound ∧ ∃ threshold : ℕ,
          ∀ address, threshold ≤ address.length →
            weight address marks *
              ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length ≤
                bound * growth ^ address.length := by
  obtain ⟨weight, properties⟩ := actual_component_cylinder_probability_weights classicalRule
    p positive belowOne fixedPoint
  obtain ⟨limit, _, _, convergence, _, _, maxima⟩ :=
    exists_actual_mass_field_subexponential classicalRule p positive belowOne fixedPoint
  have radiusPositive : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p positive belowOne fixedPoint classicalRule.scale).trans
      (rule.interior_fixed_point_spectral_dominance p positive belowOne fixedPoint
        classicalRule.massAdmissible.symmetric classicalRule.scale).2.1)
  refine ⟨weight, ?_⟩
  filter_upwards [properties, convergence, maxima] with marks weights converges bounded
  refine ⟨weights.1, weights.2.1, ?_⟩
  have rootPositive := (converges [] .connected).2.2 rfl
  have equality (address : List (Fin rule.edges × Bool)) :
      weight address marks = limit (componentEdgeAddress address) (retainedComponentState rule marks address) marks /
        (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length *
          limit [] .connected marks) := by
    have denominator := ((converges [] .connected).2.1.comp
      (tendsto_add_atTop_nat address.length)).mul_const
        (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length)
    have ratio := (converges (componentEdgeAddress address) (retainedComponentState rule marks address)).2.1.div
      denominator (mul_pos rootPositive (pow_pos radiusPositive address.length)).ne'
    have ratioConvergence : Tendsto (fun depth => markedOrientedVertexMass rule marks depth
        (componentEdgeAddress address) (retainedComponentState rule marks address) /
        markedOrientedVertexMass rule marks (depth + address.length) [] .connected)
      atTop (𝓝 (limit (componentEdgeAddress address) (retainedComponentState rule marks address) marks /
        (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length *
          limit [] .connected marks))) := by
      convert ratio using 1
      · funext depth
        simp only [Function.comp_apply, Pi.div_apply]
        rw [pow_add]
        field_simp
      · congr 1
        ring
    exact tendsto_nhds_unique (weights.2.1 address).2.2.1 ratioConvergence
  intro growth greater
  obtain ⟨threshold, estimates⟩ := bounded growth greater
  refine ⟨(limit [] .connected marks)⁻¹, inv_pos.mpr rootPositive, threshold, ?_⟩
  intro address after
  have sameLength : (componentEdgeAddress address).length = address.length := by
    simp [componentEdgeAddress]
  have bound := estimates (componentEdgeAddress address) (retainedComponentState rule marks address)
    (by simpa only [sameLength] using after)
  rw [sameLength] at bound
  rw [equality]
  have cancel : limit (componentEdgeAddress address) (retainedComponentState rule marks address) marks /
      (((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length *
        limit [] .connected marks) *
      ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ address.length =
      limit (componentEdgeAddress address) (retainedComponentState rule marks address) marks /
        limit [] .connected marks := by field_simp
  rw [cancel, mul_comm, ← div_eq_mul_inv]
  exact div_le_div_of_nonneg_right bound rootPositive.le

end
end IGSIII34.Spectral
