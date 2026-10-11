import Universality.Section5.HeterogeneousStates
import Universality.Percolation.Section5ProductDisintegration
import Universality.Percolation.LocalMassResponse

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

def heterogeneousSubstitutedLiveCount (σ τ : LiveState)
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) : ℕ := by
  classical
  exact ∑ edge : Fin outerEdges,
    (Finset.univ.filter fun child : Fin (innerEdges edge) =>
      R.heterogeneousSubstitutedChildState S σ configuration edge child = some τ).card

theorem heterogeneousSubstitutedLiveCount_eq_local (σ τ : LiveState)
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
    R.heterogeneousSubstitutedLiveCount S σ τ configuration =
      ∑ edge : Fin outerEdges,
        R.localLiveCount (S edge) (heterogeneousCoarseConfiguration S configuration)
          (configuration edge) σ τ edge := by
  classical
  unfold heterogeneousSubstitutedLiveCount
  apply Finset.sum_congr rfl
  intro edge _
  simp_rw [R.heterogeneousSubstitutedChildState_eq_local]
  unfold localLiveCount heterogeneousLocalChildState
  cases ha : R.active σ (heterogeneousCoarseConfiguration S configuration) (R.endpoint edge).1 <;>
    cases hb : R.active σ (heterogeneousCoarseConfiguration S configuration) (R.endpoint edge).2 <;>
    cases hc : (S edge).crosses (configuration edge) <;>
    simp only [heterogeneousCoarseConfiguration, hc, Bool.false_eq_true, ↓reduceIte, liveCount]
  all_goals simp

theorem heterogeneousSubstitute_conditioning (σ : LiveState)
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
    (R.heterogeneousSubstitute S).conditioning σ (heterogeneousConfigurationEquiv configuration) =
      R.conditioning σ (heterogeneousCoarseConfiguration S configuration) := by
  cases σ <;> simp only [conditioning, heterogeneousSubstitute_crosses]

theorem heterogeneousSubstitute_active (σ : LiveState)
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge))
    (vertex : R.HeterogeneousVertex S) :
    (R.heterogeneousSubstitute S).active σ (heterogeneousConfigurationEquiv configuration)
      (Fintype.equivFin _ vertex) = R.heterogeneousSubstitutedActive S σ configuration vertex := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [active, heterogeneousSubstitutedActive, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact or_congr (R.heterogeneousSubstitute_reachable_iff S configuration _ _)
    (and_congr Iff.rfl (R.heterogeneousSubstitute_reachable_iff S configuration _ _))

theorem heterogeneousSubstitute_childState (σ : LiveState)
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge))
    (edge : Fin outerEdges) (child : Fin (innerEdges edge)) :
    (R.heterogeneousSubstitute S).childState σ (heterogeneousConfigurationEquiv configuration)
      (Fintype.equivFin _ ⟨edge, child⟩) =
      R.heterogeneousSubstitutedChildState S σ configuration edge child := by
  unfold childState heterogeneousSubstitutedChildState
  rw [heterogeneousSubstitute_endpoint, heterogeneousSubstitute_active,
    heterogeneousSubstitute_active, heterogeneousConfigurationEquiv_apply]

theorem heterogeneousSubstitute_liveCount (σ τ : LiveState)
    (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
    (R.heterogeneousSubstitute S).liveCount σ τ (heterogeneousConfigurationEquiv configuration) =
      R.heterogeneousSubstitutedLiveCount S σ τ configuration := by
  classical
  unfold liveCount heterogeneousSubstitutedLiveCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Fintype.sum_sigma
    (fun pair : Σ edge : Fin outerEdges, Fin (innerEdges edge) =>
      if R.heterogeneousSubstitutedChildState S σ configuration pair.1 pair.2 = some τ then 1 else 0)]
  symm
  apply Fintype.sum_equiv (Fintype.equivFin _)
  intro pair
  rw [heterogeneousSubstitute_childState]

theorem heterogeneous_mass_numerator (p : ℝ)
    (positive : ∀ edge, 0 < (S edge).reliability p)
    (less : ∀ edge, (S edge).reliability p < 1)
    (symmetry : ∀ edge, (S edge).NetworkSymmetry)
    (source_target : ∀ edge, (symmetry edge).vertex (S edge).source = (S edge).target)
    (target_source : ∀ edge, (symmetry edge).vertex (S edge).target = (S edge).source)
    (σ τ : LiveState) :
    (∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
      if R.conditioning σ (heterogeneousCoarseConfiguration S configuration) then
        (∏ edge, bernoulliWeight p (configuration edge)) *
          R.heterogeneousSubstitutedLiveCount S σ τ configuration else 0) =
    ∑ coarse : Configuration outerEdges,
      if R.conditioning σ coarse then
        (∏ edge, if coarse edge then (S edge).reliability p else 1 - (S edge).reliability p) *
          ∑ edge, match R.childState σ coarse edge with
            | some state => (S edge).massMatrix p state τ
            | none => 0
      else 0 := by
  classical
  simp_rw [heterogeneousSubstitutedLiveCount_eq_local, Nat.cast_sum]
  have distribute (configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge)) :
      (if R.conditioning σ (heterogeneousCoarseConfiguration S configuration) then
        (∏ edge, bernoulliWeight p (configuration edge)) *
          ∑ edge, (R.localLiveCount (S edge) (heterogeneousCoarseConfiguration S configuration)
            (configuration edge) σ τ edge : ℝ) else 0) =
      ∑ edge : Fin outerEdges, (∏ e, bernoulliWeight p (configuration e)) *
        (if R.conditioning σ (heterogeneousCoarseConfiguration S configuration) then
          (R.localLiveCount (S edge) (heterogeneousCoarseConfiguration S configuration)
            (configuration edge) σ τ edge : ℝ) else 0) := by
    cases R.conditioning σ (heterogeneousCoarseConfiguration S configuration) <;>
      simp [Finset.mul_sum]
  simp_rw [distribute]
  rw [Finset.sum_comm]
  have localExpectation (edge : Fin outerEdges) :=
    heterogeneous_coarse_cell_expectation S p positive less edge
      (fun coarse edge cell => if R.conditioning σ coarse then
        (R.localLiveCount (S edge) coarse cell σ τ edge : ℝ) else 0)
  simp_rw [localExpectation, conditionalCellResponse_ite,
    R.localLiveCount_conditional_response (S _) p (symmetry _) (source_target _) (target_source _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coarse _
  cases R.conditioning σ coarse <;> simp [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  cases R.childState σ coarse edge <;> rfl

theorem heterogeneousSubstitute_conditioningProbability_common (p q : ℝ)
    (common : ∀ edge, (S edge).reliability p = q) (σ : LiveState) :
    (R.heterogeneousSubstitute S).conditioningProbability p σ = R.conditioningProbability q σ := by
  unfold conditioningProbability
  rw [← Fintype.sum_equiv heterogeneousConfigurationEquiv
    (fun configuration => if R.conditioning σ (heterogeneousCoarseConfiguration S configuration) then
      ∏ edge, bernoulliWeight p (configuration edge) else 0)
    (fun configuration => if (R.heterogeneousSubstitute S).conditioning σ configuration then
      bernoulliWeight p configuration else 0)
    (by intro configuration; rw [heterogeneousSubstitute_conditioning,
      bernoulliWeight_heterogeneousConfiguration])]
  have expectation := heterogeneous_coarse_expectation S p
    (fun coarse => if R.conditioning σ coarse then 1 else 0)
  simpa only [common, mul_ite, mul_one, mul_zero, bernoulliWeight] using expectation

theorem heterogeneousSubstitute_massMatrix_common (p q : ℝ)
    (common : ∀ edge, (S edge).reliability p = q)
    (positive : 0 < q) (less : q < 1)
    (symmetry : ∀ edge, (S edge).NetworkSymmetry)
    (source_target : ∀ edge, (symmetry edge).vertex (S edge).source = (S edge).target)
    (target_source : ∀ edge, (symmetry edge).vertex (S edge).target = (S edge).source)
    (σ τ : LiveState) :
    (R.heterogeneousSubstitute S).massMatrix p σ τ =
      (∑ coarse : Configuration outerEdges,
        if R.conditioning σ coarse then bernoulliWeight q coarse *
          ∑ edge, match R.childState σ coarse edge with
            | some state => (S edge).massMatrix p state τ
            | none => 0
        else 0) / R.conditioningProbability q σ := by
  unfold massMatrix
  rw [heterogeneousSubstitute_conditioningProbability_common R S p q common]
  congr 1
  calc
    _ = ∑ configuration : (edge : Fin outerEdges) → Configuration (innerEdges edge),
        if R.conditioning σ (heterogeneousCoarseConfiguration S configuration) then
          (∏ edge, bernoulliWeight p (configuration edge)) *
            R.heterogeneousSubstitutedLiveCount S σ τ configuration else 0 := by
      symm
      apply Fintype.sum_equiv heterogeneousConfigurationEquiv
      intro configuration
      rw [heterogeneousSubstitute_conditioning, bernoulliWeight_heterogeneousConfiguration,
        heterogeneousSubstitute_liveCount]
    _ = _ := by
      rw [heterogeneous_mass_numerator R S p
        (fun edge => by rw [common]; exact positive)
        (fun edge => by rw [common]; exact less) symmetry source_target target_source]
      simp only [common, bernoulliWeight, massMatrix]

end
end Universality.FiniteNetwork
