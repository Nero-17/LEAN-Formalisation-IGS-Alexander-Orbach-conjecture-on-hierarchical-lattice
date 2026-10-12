import IGSIII34.ResistanceLimit.RadiusMesh
import IGSIII34.ResistanceLimit.RadiusMoments
import IGSIII34.Percolation.Continuation.NaturalPhysicalOmegaCompletion
import Mathlib.Topology.Instances.Rat

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII34.Percolation
open MeasureTheory Filter
open scoped ENNReal Topology BigOperators

private theorem finite_prefix_real_bound (edges start : ℕ)
    (values : List (Fin edges) → Bool → ℝ) :
    ∃ bound : ℝ, ∀ address opened, address.length < start → values address opened ≤ bound := by
  classical
  let indexed : (Σ depth : Fin start, (Fin depth.val → Fin edges) × Bool) → ℝ :=
    fun item => values (List.ofFn item.2.1) item.2.2
  obtain ⟨bound, bounded⟩ := (Set.finite_range indexed).bddAbove
  refine ⟨bound, ?_⟩
  intro address opened before
  have estimate := bounded (Set.mem_range_self
    (⟨⟨address.length, before⟩, (address.get, opened)⟩ :
      Σ depth : Fin start, (Fin depth.val → Fin edges) × Bool))
  simpa only [indexed, List.ofFn_get] using estimate

theorem ae_markedElectricalRadiusSupremum_exponential_fixed_cluster
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth)
    (slack : ℝ) (slackGreaterThanOne : 1 < slack) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∃ bound : ℝ, 0 < bound ∧ ∀ address opened,
        markedElectricalRadiusSupremum rule growth address opened marks ≤ bound * slack ^ address.length := by
  have growthPositive : 0 < growth := zero_lt_one.trans growthGreaterThanOne
  let intermediate : ℝ := (1 + min slack growth) / 2
  have minimumGreater : 1 < min slack growth := lt_min slackGreaterThanOne growthGreaterThanOne
  have intermediateGreater : 1 < intermediate := by dsimp [intermediate]; linarith
  have intermediateBelowSlack : intermediate < slack := by
    have := min_le_left slack growth
    dsimp [intermediate]
    linarith
  have intermediateBelowGrowth : intermediate < growth := by
    have := min_le_right slack growth
    dsimp [intermediate]
    linarith
  have etaPositive : 0 < intermediate / growth := div_pos (zero_lt_one.trans intermediateGreater) growthPositive
  have etaBelowOne : intermediate / growth < 1 := (div_lt_one growthPositive).mpr intermediateBelowGrowth
  have productIdentity : growth * (intermediate / growth) = intermediate := by field_simp
  have mesh := ae_uniform_actual_electrical_mesh_fixed_cluster rule classicalRule p positive belowOne fixedPoint
    constant growth constantPositive growthGreaterThanOne growthBounds endpoint endpointFixed membership
    (intermediate / growth) etaPositive etaBelowOne (by rw [productIdentity]; exact intermediateGreater)
  filter_upwards [mesh] with marks mesh
  obtain ⟨start, estimates⟩ := mesh
  let coefficient : ℝ := (rule.edges + 1 : ℝ) / (1 - intermediate / growth)
  have coefficientPositive : 0 < coefficient := by
    dsimp [coefficient]
    exact div_pos (by positivity) (sub_pos.mpr etaBelowOne)
  have eventualBound (address : List (Fin rule.edges)) (opened : Bool) (after : start ≤ address.length) :
      markedElectricalRadiusSupremum rule growth address opened marks ≤ coefficient * slack ^ address.length := by
    apply ciSup_le
    intro depth
    calc
      markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1) =
          (markedElectricalRadius rule marks depth address opened / growth ^ (depth + 1 + address.length)) *
            growth ^ address.length := by
        field_simp [growthPositive.ne', pow_add, pow_succ]
        ring
      _ ≤ (coefficient * (intermediate / growth) ^ address.length) * growth ^ address.length :=
        mul_le_mul_of_nonneg_right (estimates address opened depth after) (pow_pos growthPositive _).le
      _ = coefficient * intermediate ^ address.length := by
        rw [mul_assoc, ← mul_pow]
        congr 1
        congr 1
        field_simp
      _ ≤ coefficient * slack ^ address.length :=
        mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (zero_lt_one.trans intermediateGreater).le intermediateBelowSlack.le _) coefficientPositive.le
  obtain ⟨initialBound, initialEstimates⟩ := finite_prefix_real_bound rule.edges start
    (fun address opened => markedElectricalRadiusSupremum rule growth address opened marks)
  refine ⟨max (max initialBound coefficient) 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro address opened
  by_cases after : start ≤ address.length
  · exact (eventualBound address opened after).trans (mul_le_mul_of_nonneg_right
      ((le_max_right initialBound coefficient).trans (le_max_left _ _)) (pow_nonneg (zero_lt_one.trans slackGreaterThanOne).le _))
  · have initial := initialEstimates address opened (Nat.lt_of_not_ge after)
    have boundPositive : 0 ≤ max (max initialBound coefficient) 1 := (zero_le_one.trans (le_max_right _ _))
    exact initial.trans (((le_max_left initialBound coefficient).trans (le_max_left _ _)).trans
      (le_mul_of_one_le_right boundPositive (one_le_pow₀ slackGreaterThanOne.le)))

theorem ae_markedElectricalRadiusSupremum_subexponential_fixed_cluster
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (constant growth : ℝ)
    (constantPositive : 0 < constant) (growthGreaterThanOne : 1 < growth)
    (growthBounds : ∀ depth, growth ^ depth ≤
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ∧
      (electricalOrbitScale rule p positive belowOne fixedPoint depth : ℝ) ≤ constant⁻¹ * growth ^ depth)
    (endpoint : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
    (endpointFixed : normalizedElectricalTransferLp rule p positive belowOne fixedPoint 2 growth endpoint = endpoint)
    (membership : endpoint ∈ electricalOmegaSet rule p positive belowOne fixedPoint growth) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ bound : ℝ, 0 < bound ∧ ∀ address opened,
        markedElectricalRadiusSupremum rule growth address opened marks ≤ bound * slack ^ address.length := by
  have rationalBounds : ∀ slack : ℚ, ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      1 < (slack : ℝ) → ∃ bound : ℝ, 0 < bound ∧ ∀ address opened,
        markedElectricalRadiusSupremum rule growth address opened marks ≤ bound * (slack : ℝ) ^ address.length := by
    intro slack
    by_cases greater : 1 < (slack : ℝ)
    · exact (ae_markedElectricalRadiusSupremum_exponential_fixed_cluster rule classicalRule p positive belowOne fixedPoint
        constant growth constantPositive growthGreaterThanOne growthBounds endpoint endpointFixed membership
        (slack : ℝ) greater).mono (fun _ bounded _ => bounded)
    · exact Filter.Eventually.of_forall (fun _ impossible => (greater impossible).elim)
  filter_upwards [ae_all_iff.mpr rationalBounds] with marks bounded
  intro slack greater
  obtain ⟨rational, aboveOne, belowSlack⟩ := exists_rat_btwn greater
  obtain ⟨bound, boundPositive, estimates⟩ := bounded rational aboveOne
  refine ⟨bound, boundPositive, ?_⟩
  intro address opened
  exact (estimates address opened).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (zero_lt_one.trans aboveOne).le belowSlack.le _) boundPositive.le)

/-- The natural electrical witness discharges all analytic inputs from the
original finite classical rule; no radius or diameter bounds are premises. -/
theorem ae_natural_markedElectricalRadiusSupremum_subexponential_completion
    (rule : Rule) (classicalRule : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint) :
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
      ∀ slack : ℝ, 1 < slack → ∃ bound : ℝ, 0 < bound ∧ ∀ address opened,
        markedElectricalRadiusSupremum rule natural.growth address opened marks ≤
          bound * slack ^ address.length := by
  obtain ⟨constant, constantPositive, growthBounds, membership, endpointFixed⟩ :=
    natural_physical_omega_witness_completion rule classicalRule p positive belowOne fixedPoint natural
  exact ae_markedElectricalRadiusSupremum_subexponential_fixed_cluster rule classicalRule p positive belowOne fixedPoint
    constant natural.growth constantPositive natural.aboveOne growthBounds
    (natural.amplitude • natural.field) endpointFixed membership

end
end IGSIII34.ResistanceLimit
