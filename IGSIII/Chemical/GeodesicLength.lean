import IGSIII.Chemical.GeodesicOneSided
import IGSIII.Probability.FiniteHolder
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-! An inverse-moment estimate for the length of an actual selected geodesic. -/

set_option autoImplicit false

namespace IGSIII.Chemical

open IGSIII.Probability PathFamily
open scoped BigOperators

variable {Edge Outcome : Type*} [Fintype Edge] [DecidableEq Edge] [Fintype Outcome]

noncomputable def inverseEnvelope (cost : Edge → ℝ) (power : ℝ) : ℝ :=
  (∑ edge, (cost edge)⁻¹ ^ power) ^ (1 / power)

theorem inverseEnvelope_nonnegative (cost : Edge → ℝ) {power : ℝ}
    (positive : ∀ edge, 0 < cost edge) : 0 ≤ inverseEnvelope cost power :=
  Real.rpow_nonneg (Finset.sum_nonneg (fun edge _ =>
    Real.rpow_nonneg (inv_nonneg.mpr (positive edge).le) _)) _

theorem inverse_le_inverseEnvelope (cost : Edge → ℝ) {power : ℝ}
    (powerPositive : 0 < power) (positive : ∀ edge, 0 < cost edge) (edge : Edge) :
    (cost edge)⁻¹ ≤ inverseEnvelope cost power := by
  have sumNonnegative : 0 ≤ ∑ edge, (cost edge)⁻¹ ^ power :=
    Finset.sum_nonneg (fun edge _ => Real.rpow_nonneg (inv_nonneg.mpr (positive edge).le) _)
  unfold inverseEnvelope
  rw [one_div]
  apply (Real.le_rpow_inv_iff_of_pos (inv_nonneg.mpr (positive edge).le)
    sumNonnegative powerPositive).mpr
  exact Finset.single_le_sum (fun other _ =>
    Real.rpow_nonneg (inv_nonneg.mpr (positive other).le) _) (Finset.mem_univ edge)

theorem PathFamily.geodesic_card_le_shortest_mul_inverseEnvelope
    (family : PathFamily Edge) (cost : Edge → ℝ) {power : ℝ}
    (powerPositive : 0 < power) (positive : ∀ edge, 0 < cost edge) :
    ((family.minimizingPath cost).card : ℝ) ≤ family.shortest cost * inverseEnvelope cost power := by
  have perEdge (edge : Edge) : 1 ≤ cost edge * inverseEnvelope cost power := by
    have bound := mul_le_mul_of_nonneg_left
      (inverse_le_inverseEnvelope cost powerPositive positive edge) (positive edge).le
    simpa only [mul_inv_cancel₀ (positive edge).ne'] using bound
  calc
    _ = ∑ _edge ∈ family.minimizingPath cost, (1 : ℝ) := by simp
    _ ≤ ∑ edge ∈ family.minimizingPath cost, cost edge * inverseEnvelope cost power :=
      Finset.sum_le_sum (fun edge _ => perEdge edge)
    _ = family.shortest cost * inverseEnvelope cost power := by
      rw [← Finset.sum_mul]
      rw [← pathCost, family.minimizingPath_cost]

theorem finiteMean_inverseEnvelope_sq_le
    (weight : Outcome → ℝ) (cost : Outcome → Edge → ℝ) {power : ℝ}
    (powerAtLeastTwo : 2 ≤ power)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (positive : ∀ outcome edge, 0 < cost outcome edge) :
    finiteMean weight (fun outcome => inverseEnvelope (cost outcome) power ^ 2) ≤
      (finiteMean weight (fun outcome => ∑ edge, (cost outcome edge)⁻¹ ^ power)) ^ (2 / power) := by
  have powerPositive : 0 < power := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) powerAtLeastTwo
  have exponentNonnegative : 0 ≤ 2 / power := div_nonneg (by norm_num) powerPositive.le
  have exponentAtMostOne : 2 / power ≤ 1 := (div_le_one powerPositive).mpr powerAtLeastTwo
  have sumNonnegative (outcome : Outcome) : 0 ≤ ∑ edge, (cost outcome edge)⁻¹ ^ power :=
    Finset.sum_nonneg (fun edge _ => Real.rpow_nonneg (inv_nonneg.mpr (positive outcome edge).le) _)
  have envelopeSquared (outcome : Outcome) :
      inverseEnvelope (cost outcome) power ^ 2 =
        (∑ edge, (cost outcome edge)⁻¹ ^ power) ^ (2 / power) := by
    unfold inverseEnvelope
    rw [← Real.rpow_natCast, ← Real.rpow_mul (sumNonnegative outcome)]
    congr 1
    norm_num
    ring
  have bound := (Real.concaveOn_rpow exponentNonnegative exponentAtMostOne).le_map_sum
    (t := Finset.univ) (w := weight) (p := fun outcome => ∑ edge, (cost outcome edge)⁻¹ ^ power)
    (fun outcome _ => weightNonnegative outcome) normalized (fun outcome _ => sumNonnegative outcome)
  simpa only [finiteMean, envelopeSquared, smul_eq_mul] using bound

theorem finiteMean_geodesic_card_le_inverse_moment
    (family : PathFamily Edge) (weight : Outcome → ℝ) (cost : Outcome → Edge → ℝ)
    {power : ℝ} (powerAtLeastTwo : 2 ≤ power)
    (weightNonnegative : ∀ outcome, 0 ≤ weight outcome)
    (normalized : ∑ outcome, weight outcome = 1)
    (positive : ∀ outcome edge, 0 < cost outcome edge) :
    finiteMean weight (fun outcome => ((family.minimizingPath (cost outcome)).card : ℝ)) ≤
      (finiteMean weight (fun outcome => family.shortest (cost outcome) ^ 2)) ^ (1 / (2 : ℝ)) *
        (finiteMean weight (fun outcome => ∑ edge, (cost outcome edge)⁻¹ ^ power)) ^ (1 / power) := by
  have powerPositive : 0 < power := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) powerAtLeastTwo
  have inverseNonnegative : 0 ≤ finiteMean weight
      (fun outcome => ∑ edge, (cost outcome edge)⁻¹ ^ power) := by
    unfold finiteMean
    apply Finset.sum_nonneg
    intro outcome _
    exact mul_nonneg (weightNonnegative outcome) (Finset.sum_nonneg
      (fun edge _ => Real.rpow_nonneg (inv_nonneg.mpr (positive outcome edge).le) _))
  have envelopeBound := finiteMean_inverseEnvelope_sq_le weight cost powerAtLeastTwo
    weightNonnegative normalized positive
  calc
    _ ≤ finiteMean weight (fun outcome => family.shortest (cost outcome) *
          inverseEnvelope (cost outcome) power) := by
      unfold finiteMean
      apply Finset.sum_le_sum
      intro outcome _
      exact mul_le_mul_of_nonneg_left
        (family.geodesic_card_le_shortest_mul_inverseEnvelope (cost outcome) powerPositive (positive outcome))
        (weightNonnegative outcome)
    _ ≤ (finiteMean weight (fun outcome => family.shortest (cost outcome) ^ 2)) ^ (1 / (2 : ℝ)) *
          (finiteMean weight (fun outcome => inverseEnvelope (cost outcome) power ^ 2)) ^ (1 / (2 : ℝ)) := by
      simpa only [Real.rpow_two] using finiteMean_mul_le_holder weight
        (fun outcome => family.shortest (cost outcome))
        (fun outcome => inverseEnvelope (cost outcome) power) Real.HolderConjugate.two_two
        weightNonnegative (fun outcome => family.shortest_nonneg (fun edge => (positive outcome edge).le))
        (fun outcome => inverseEnvelope_nonnegative _ (positive outcome))
    _ ≤ (finiteMean weight (fun outcome => family.shortest (cost outcome) ^ 2)) ^ (1 / (2 : ℝ)) *
          ((finiteMean weight (fun outcome => ∑ edge, (cost outcome edge)⁻¹ ^ power)) ^
            (2 / power)) ^ (1 / (2 : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow _ envelopeBound (by norm_num))
        (Real.rpow_nonneg (Finset.sum_nonneg (fun outcome _ =>
          mul_nonneg (weightNonnegative outcome) (sq_nonneg _))) _)
      exact Finset.sum_nonneg (fun outcome _ => mul_nonneg (weightNonnegative outcome) (sq_nonneg _))
    _ = _ := by
      rw [← Real.rpow_mul inverseNonnegative]
      congr 2
      ring

end IGSIII.Chemical
