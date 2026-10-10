import Universality.Percolation.DistanceWindowPairs

namespace Universality
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000

theorem finite_product_two_local_moments {index outcome : Type*}
    [Fintype index] [DecidableEq index] [Fintype outcome]
    (weight response : index → outcome → ℝ)
    (hnormalized : ∀ i, ∑ value, weight i value = 1)
    (first second : index) (hdistinct : first ≠ second) :
    (∑ values : index → outcome, (∏ i, weight i (values i)) *
      response first (values first) * response second (values second)) =
      (∑ value, weight first value * response first value) *
        (∑ value, weight second value * response second value) := by
  classical
  have hfactor (values : index → outcome) :
      (∏ i, weight i (values i)) * response first (values first) * response second (values second) =
      ∏ i, weight i (values i) * (if i = first then response i (values i) else 1) *
        (if i = second then response i (values i) else 1) := by
    simp only [Finset.prod_mul_distrib]
    simp
  simp_rw [hfactor]
  rw [← Fintype.prod_sum (fun i value => weight i value *
    (if i = first then response i value else 1) *
    (if i = second then response i value else 1))]
  have hlocal (i : index) :
      (∑ value, weight i value * (if i = first then response i value else 1) *
        (if i = second then response i value else 1)) =
      (if i = first then ∑ value, weight i value * response i value else 1) *
        (if i = second then ∑ value, weight i value * response i value else 1) := by
    by_cases hfirst : i = first
    · subst i; simp [hdistinct]
    · by_cases hsecond : i = second
      · subst i; simp [hfirst]
      · simp [hfirst, hsecond, hnormalized]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib]
  simp

end
end Universality

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- A genuine all-crossing coarse configuration supplies the product of two
independent actual connected child masses inside the prescribed window. -/
theorem expected_connected_window_pairs_lower
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (first second : Fin outerEdges) (hdistinct : first ≠ second) (lower upper : ℝ)
    (hwindow : ∀ u v : S.InteriorVertex,
      lower ≤ ((R.substitute S).fullGraph.dist (R.cellEmbedding S first u.val)
        (R.cellEmbedding S second v.val) : ℝ) ∧
      ((R.substitute S).fullGraph.dist (R.cellEmbedding S first u.val)
        (R.cellEmbedding S second v.val) : ℝ) ≤ upper) :
    bernoulliWeight (S.reliability p) (fun _ : Fin outerEdges => true) *
        (S.conditionalVertexMass p .connected) ^ 2 ≤
      ∑ configuration : Configuration (outerEdges * innerEdges), bernoulliWeight p configuration *
        (((R.substitute S).connectedDistanceWindowPairs configuration lower upper).card : ℝ) := by
  let count (cells : Fin outerEdges → Configuration innerEdges) : ℝ :=
    ((R.substitute S).connectedDistanceWindowPairs (substitutionConfigurationEquiv cells) lower upper).card
  have hdisintegration :
      (∑ configuration : Configuration (outerEdges * innerEdges), bernoulliWeight p configuration *
        (((R.substitute S).connectedDistanceWindowPairs configuration lower upper).card : ℝ)) =
      ∑ coarse : Configuration outerEdges, bernoulliWeight (S.reliability p) coarse *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) * count cells := by
    rw [← substitutionConfigurationEquiv.sum_comp]
    simp only [bernoulliWeight_substitutionConfiguration]
    exact S.coarse_substitution_observable p hpositive hless (fun _ cells => count cells)
  rw [hdisintegration]
  have hpoint (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ edge, S.conditionalCellWeight p true (cells edge)) *
          (S.internalSelectedMass true false (cells first) : ℝ) *
          (S.internalSelectedMass true false (cells second) : ℝ) ≤
        (∏ edge, S.conditionalCellWeight p true (cells edge)) * count cells := by
    by_cases hcrossing : ∀ edge, S.crosses (cells edge) = true
    · rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _
        (Finset.prod_nonneg (fun _ _ => S.conditionalCellWeight_nonneg hp hp' _ _))
      have hbound := R.connectedDistanceWindowPairs_card_ge_crossing_masses S houter cells
        hcrossing first second lower upper hwindow
      dsimp only [count]
      exact_mod_cast hbound
    · obtain ⟨edge, hedge⟩ := not_forall.mp hcrossing
      have hzero : (∏ edge, S.conditionalCellWeight p true (cells edge)) = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ edge)
        simp [conditionalCellWeight, hedge]
      simp only [hzero, zero_mul, le_refl]
  have hproduct := finite_product_two_local_moments
    (fun (_ : Fin outerEdges) cell => S.conditionalCellWeight p true cell)
    (fun (_ : Fin outerEdges) cell => (S.internalSelectedMass true false cell : ℝ))
    (fun _ => S.sum_conditionalCellWeight p hpositive hless true) first second hdistinct
  have hconditional : (S.conditionalVertexMass p .connected) ^ 2 ≤
      ∑ cells : Fin outerEdges → Configuration innerEdges,
        (∏ edge, S.conditionalCellWeight p true (cells edge)) * count cells := by
    calc
      _ = ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ edge, S.conditionalCellWeight p true (cells edge)) *
            (S.internalSelectedMass true false (cells first) : ℝ) *
            (S.internalSelectedMass true false (cells second) : ℝ) := by
        have hmean : S.conditionalVertexMass p .connected =
            ∑ cell, S.conditionalCellWeight p true cell *
              (S.internalSelectedMass true false cell : ℝ) := rfl
        rw [hmean, pow_two]
        exact hproduct.symm
      _ ≤ _ := Finset.sum_le_sum (fun cells _ => hpoint cells)
  have hnonnegative (coarse : Configuration outerEdges) :
      0 ≤ bernoulliWeight (S.reliability p) coarse *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge)) * count cells := by
    apply mul_nonneg (bernoulliWeight_nonneg hpositive.le hless.le _)
    apply Finset.sum_nonneg
    intro cells _
    exact mul_nonneg (Finset.prod_nonneg (fun edge _ => S.conditionalCellWeight_nonneg hp hp' _ _))
      (Nat.cast_nonneg _)
  calc
    _ ≤ bernoulliWeight (S.reliability p) (fun _ : Fin outerEdges => true) *
        ∑ cells : Fin outerEdges → Configuration innerEdges,
          (∏ edge, S.conditionalCellWeight p true (cells edge)) * count cells :=
      mul_le_mul_of_nonneg_left hconditional (bernoulliWeight_nonneg hpositive.le hless.le _)
    _ ≤ _ := Finset.single_le_sum (fun coarse _ => hnonnegative coarse)
      (Finset.mem_univ (fun _ : Fin outerEdges => true))

end
end Universality.FiniteNetwork
