import IGSIII34.Resistance.RandomComparison
import IGSIII34.Resistance.Continuity

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.Resistance.FiniteNetwork
noncomputable section

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem minimizing_current_difference_energy_identity (network : FiniteNetwork Vertex Edge)
    {resistance first second : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (firstFlow : first ∈ network.unitFlows) (secondFlow : second ∈ network.unitFlows)
    (firstMinimal : energy resistance first = network.effectiveResistance resistance) :
    energy resistance (fun edge => second edge - first edge) =
      energy resistance second - energy resistance first := by
  have orthogonal := network.minimizing_current_orthogonal positive firstFlow firstMinimal
    (network.unitFlow_sub_zero_divergence secondFlow firstFlow)
  have identity := energy_perturbation resistance first (fun edge => second edge - first edge) 1
  have currentIdentity : (fun edge => first edge + 1 * (second edge - first edge)) = second := by
    funext edge
    ring
  rw [currentIdentity, orthogonal] at identity
  linarith

theorem minimizing_current_unique (network : FiniteNetwork Vertex Edge)
    {resistance first second : Edge → ℝ} (positive : ∀ edge, 0 < resistance edge)
    (firstFlow : first ∈ network.unitFlows) (secondFlow : second ∈ network.unitFlows)
    (firstMinimal : energy resistance first = network.effectiveResistance resistance)
    (secondMinimal : energy resistance second = network.effectiveResistance resistance) :
    first = second := by
  have identity := network.minimizing_current_difference_energy_identity positive
    firstFlow secondFlow firstMinimal
  rw [firstMinimal, secondMinimal, sub_self] at identity
  have zeroDifference := (energy_eq_zero_iff positive).mp identity
  funext edge
  have := zeroDifference edge
  linarith

theorem minimizingCurrent_difference_energy_bound (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (first second : Edge → ℝ)
    (firstPositive : ∀ edge, 0 < first edge) (secondPositive : ∀ edge, 0 < second edge) :
    energy first (fun edge => network.minimizingCurrent connected second secondPositive edge -
      network.minimizingCurrent connected first firstPositive edge) ≤
      2 * ∑ edge, |first edge - second edge| := by
  rw [network.minimizing_current_difference_energy_identity firstPositive
    (network.minimizingCurrent_unitFlow connected first firstPositive)
    (network.minimizingCurrent_unitFlow connected second secondPositive)
    (network.minimizingCurrent_energy connected first firstPositive)]
  have trialBound := trial_energy_difference_le_sum_abs second first
    (network.minimizingCurrent connected second secondPositive)
    (network.minimizing_current_abs_le_one secondPositive
      (network.minimizingCurrent_unitFlow connected second secondPositive)
      (network.minimizingCurrent_energy connected second secondPositive))
  rw [network.minimizingCurrent_energy connected second secondPositive] at trialBound
  rw [network.minimizingCurrent_energy connected first firstPositive]
  have resistanceBound := network.effectiveResistance_le_add_sum_abs connected firstPositive secondPositive
  simp_rw [abs_sub_comm (second _) (first _)] at resistanceBound
  linarith

def positiveCurrent (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target)
    (resistance : {resistance : Edge → ℝ // ∀ edge, 0 < resistance edge}) : Edge → ℝ :=
  network.minimizingCurrent connected resistance.val resistance.property

theorem positiveCurrent_continuous (network : FiniteNetwork Vertex Edge)
    (connected : network.graph.Reachable network.source network.target) :
    Continuous (network.positiveCurrent connected) := by
  apply continuous_pi
  intro changed
  apply continuous_iff_continuousAt.mpr
  intro first
  apply Metric.continuousAt_iff.mpr
  intro tolerance tolerancePositive
  let radius := tolerance ^ 2 * first.val changed / (4 * (Fintype.card Edge + 1 : ℝ))
  have radiusPositive : 0 < radius := by
    dsimp [radius]
    exact div_pos (mul_pos (sq_pos_of_pos tolerancePositive) (first.property changed)) (by positivity)
  refine ⟨radius, radiusPositive, ?_⟩
  intro second close
  have energyBound := network.minimizingCurrent_difference_energy_bound connected
    first.val second.val first.property second.property
  have singleBound := Finset.single_le_sum (fun edge _ =>
    mul_nonneg (first.property edge).le (sq_nonneg
      (network.positiveCurrent connected second edge - network.positiveCurrent connected first edge)))
    (Finset.mem_univ changed)
  have sumBound : (∑ edge, |first.val edge - second.val edge|) ≤
      (Fintype.card Edge : ℝ) * dist first second := by
    calc
      _ ≤ ∑ _edge : Edge, dist first.val second.val := by
        apply Finset.sum_le_sum
        intro edge _
        simpa only [Real.dist_eq] using dist_le_pi_dist first.val second.val edge
      _ = _ := by simp [nsmul_eq_mul, Subtype.dist_eq]
  have scaledClose := (mul_lt_mul_of_pos_right close (by positivity : 0 < (4 * (Fintype.card Edge + 1 : ℝ))))
  have radiusIdentity : radius * (4 * (Fintype.card Edge + 1 : ℝ)) = tolerance ^ 2 * first.val changed := by
    dsimp [radius]
    field_simp
  rw [radiusIdentity] at scaledClose
  rw [dist_comm second first] at scaledClose
  change first.val changed *
    (network.positiveCurrent connected second changed - network.positiveCurrent connected first changed) ^ 2 ≤
    energy first.val (fun edge => network.positiveCurrent connected second edge -
      network.positiveCurrent connected first edge) at singleBound
  have squareSmall :
      (network.positiveCurrent connected second changed - network.positiveCurrent connected first changed) ^ 2 <
        tolerance ^ 2 := by
    change energy first.val (fun edge => network.positiveCurrent connected second edge -
      network.positiveCurrent connected first edge) ≤ _ at energyBound
    nlinarith [first.property changed, (dist_nonneg : 0 ≤ dist first second),
      (by positivity : 0 ≤ (Fintype.card Edge : ℝ))]
  rw [Real.dist_eq]
  nlinarith [abs_nonneg (network.positiveCurrent connected second changed -
    network.positiveCurrent connected first changed),
    sq_abs (network.positiveCurrent connected second changed - network.positiveCurrent connected first changed)]

end
end IGSIII34.Resistance.FiniteNetwork
