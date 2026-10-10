import Universality.Percolation.FirstMoments

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem conditioningProbability_pos_iff {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (σ : LiveState) :
    0 < R.conditioningProbability p σ ↔ ∃ ω, R.conditioning σ ω = true := by
  unfold conditioningProbability
  rw [Finset.sum_pos_iff_of_nonneg]
  · simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ω, hω⟩
      refine ⟨ω, ?_⟩
      by_contra h
      simp [h] at hω
    · rintro ⟨ω, hω⟩
      exact ⟨ω, by simpa only [hω, ↓reduceIte] using bernoulliWeight_pos hp hp' ω⟩
  · intro ω _
    split
    · exact (bernoulliWeight_pos hp hp' ω).le
    · exact le_rfl

theorem liveCount_pos_iff (σ τ : LiveState) (ω : Configuration edges) :
    0 < R.liveCount σ τ ω ↔ ∃ edge, R.childState σ ω edge = some τ := by
  simp only [liveCount, Finset.card_pos, Finset.nonempty_def,
    Finset.mem_filter, Finset.mem_univ, true_and]

theorem massMatrix_numerator_pos_iff {p : ℝ} (hp : 0 < p) (hp' : p < 1)
    (σ τ : LiveState) :
    (0 < ∑ ω : Configuration edges, if R.conditioning σ ω then
      bernoulliWeight p ω * R.liveCount σ τ ω else 0) ↔
      ∃ ω edge, R.conditioning σ ω = true ∧ R.childState σ ω edge = some τ := by
  rw [Finset.sum_pos_iff_of_nonneg]
  · simp only [Finset.mem_univ, true_and]
    constructor
    · rintro ⟨ω, hω⟩
      have hc : R.conditioning σ ω = true := by
        by_contra h
        simp [h] at hω
      rw [hc, if_pos rfl, mul_pos_iff_of_pos_left (bernoulliWeight_pos hp hp' ω)] at hω
      have hcount : 0 < R.liveCount σ τ ω := by exact_mod_cast hω
      obtain ⟨edge, he⟩ := (R.liveCount_pos_iff σ τ ω).mp hcount
      exact ⟨ω, edge, hc, he⟩
    · rintro ⟨ω, edge, hc, he⟩
      refine ⟨ω, ?_⟩
      rw [hc, if_pos rfl]
      apply mul_pos (bernoulliWeight_pos hp hp' ω)
      exact_mod_cast (R.liveCount_pos_iff σ τ ω).mpr ⟨edge, he⟩
  · intro ω _
    split
    · exact mul_nonneg (bernoulliWeight_pos hp hp' ω).le (Nat.cast_nonneg _)
    · exact le_rfl

/-- Positivity is a finite configuration property, independent of the
particular probability in the open interval. -/
theorem massMatrix_pos_iff {p : ℝ} (hp : 0 < p) (hp' : p < 1) (σ τ : LiveState) :
    0 < R.massMatrix p σ τ ↔
      ∃ ω edge, R.conditioning σ ω = true ∧ R.childState σ ω edge = some τ := by
  constructor
  · intro hpositive
    have hdenom : 0 < R.conditioningProbability p σ := by
      have hn := R.conditioningProbability_nonneg hp.le hp'.le σ
      by_contra h
      have hz : R.conditioningProbability p σ = 0 := le_antisymm (le_of_not_gt h) hn
      simp [massMatrix, hz] at hpositive
    apply (R.massMatrix_numerator_pos_iff hp hp' σ τ).mp
    exact (div_pos_iff_of_pos_right hdenom).mp hpositive
  · intro hwitness
    have hdenom : 0 < R.conditioningProbability p σ :=
      (R.conditioningProbability_pos_iff hp hp' σ).mpr
        (by obtain ⟨ω, edge, hc, _⟩ := hwitness; exact ⟨ω, hc⟩)
    exact div_pos ((R.massMatrix_numerator_pos_iff hp hp' σ τ).mpr hwitness) hdenom

theorem massMatrix_pos_probability_independent {p q : ℝ}
    (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1) (σ τ : LiveState) :
    0 < R.massMatrix p σ τ ↔ 0 < R.massMatrix q σ τ := by
  rw [R.massMatrix_pos_iff hp hp', R.massMatrix_pos_iff hq hq']

end
end Universality.FiniteNetwork
