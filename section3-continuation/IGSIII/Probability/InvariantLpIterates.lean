import IGSIII.Probability.InvariantEnvelope
import IGSIII.Probability.LpRealOrder

set_option autoImplicit false

namespace IGSIII.Probability

open MeasureTheory Set Filter
open scoped Topology ENNReal

variable {Sample : Type*} [MeasurableSpace Sample] {measure : Measure Sample}

theorem lp_iterate_smul (map : Lp ℝ 2 measure → Lp ℝ 2 measure)
    (homogeneous : ∀ scalar : ℝ, 0 ≤ scalar → ∀ value, map (scalar • value) = scalar • map value)
    (scalar : ℝ) (nonnegative : 0 ≤ scalar) (value : Lp ℝ 2 measure) (depth : ℕ) :
    map^[depth] (scalar • value) = scalar • map^[depth] value := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
    rw [Function.iterate_succ_apply', inductionHypothesis, homogeneous scalar nonnegative,
      Function.iterate_succ_apply']

theorem invariant_glb_iterate_bounds (map : Lp ℝ 2 measure → Lp ℝ 2 measure)
    (monotone : Monotone map)
    (homogeneous : ∀ scalar : ℝ, 0 ≤ scalar → ∀ value, map (scalar • value) = scalar • map value)
    (family : Set (Lp ℝ 2 measure)) (invariant : Set.MapsTo map family family)
    (onto : Set.SurjOn map family family) (constant : ℝ) (constantPositive : 0 < constant)
    (comparison : ∀ first ∈ family, ∀ second ∈ family, first ≤ constant • second)
    (base : Lp ℝ 2 measure) (baseMember : base ∈ family)
    (envelope : Lp ℝ 2 measure) (greatestLowerBound : IsGLB family envelope) (depth : ℕ) :
    (constant⁻¹ * constant⁻¹) • base ≤ map^[depth] envelope ∧ map^[depth] envelope ≤ base := by
  have lowerBound : constant⁻¹ • base ≤ envelope := by
    apply greatestLowerBound.2
    intro value member
    exact lp_inv_smul_le_of_le_smul constant constantPositive (comparison base baseMember value member)
  have orbitMember := iterate_mem_of_invariant map family invariant base baseMember depth
  have baseBelowOrbit : constant⁻¹ • base ≤ map^[depth] base :=
    lp_inv_smul_le_of_le_smul constant constantPositive (comparison base baseMember _ orbitMember)
  have scaledLower : (constant⁻¹ * constant⁻¹) • base ≤ constant⁻¹ • map^[depth] base := by
    rw [← smul_smul]
    exact lp_smul_mono baseBelowOrbit constant⁻¹ (inv_nonneg.mpr constantPositive.le)
  have orbitLower := monotone.iterate depth lowerBound
  rw [lp_iterate_smul map homogeneous constant⁻¹ (inv_nonneg.mpr constantPositive.le) base depth] at orbitLower
  refine ⟨scaledLower.trans orbitLower, ?_⟩
  exact ((antitone_iterates_of_invariant_glb map monotone family onto envelope greatestLowerBound)
    (Nat.zero_le depth)).trans (greatestLowerBound.1 baseMember)

theorem fixed_of_continuous_iterate_limit {Space : Type*} [TopologicalSpace Space]
    [T2Space Space] (map : Space → Space) (continuous : Continuous map)
    (seed limit : Space) (convergence : Tendsto (fun depth : ℕ => map^[depth] seed) atTop (𝓝 limit)) :
    map limit = limit := by
  have mapped := (continuous.tendsto limit).comp convergence
  have shifted := convergence.comp (Filter.tendsto_add_atTop_nat 1)
  apply tendsto_nhds_unique mapped
  convert shifted using 1
  funext depth
  exact (Function.iterate_succ_apply' map depth seed).symm

end IGSIII.Probability
