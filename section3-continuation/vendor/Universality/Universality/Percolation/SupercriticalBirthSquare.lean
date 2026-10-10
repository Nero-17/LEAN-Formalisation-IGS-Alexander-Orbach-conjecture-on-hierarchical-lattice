import Universality.Probability.RareFamilyMoment
import Universality.Percolation.SupercriticalBirthBound

namespace Universality.FiniteNetwork
noncomputable section
variable {outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem expectedBirthClusterPower_square_le_failure
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (hconnected : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) (order : ℕ) :
    R.expectedBirthClusterPower S p order ^ 2 ≤
      (outerVertices : ℝ) * ((outerEdges : ℝ) * (1 - S.reliability p)) *
        R.expectedBirthClusterPower S p (2 * order) := by
  have hlocal : (∑ configuration : Configuration innerEdges, bernoulliWeight p configuration *
      (if S.crosses configuration then (0 : ℝ) else 1)) = 1 - S.reliability p := by
    calc
      _ = ∑ configuration : Configuration innerEdges,
          (bernoulliWeight p configuration -
            if S.crosses configuration then bernoulliWeight p configuration else 0) := by
        apply Finset.sum_congr rfl
        intro configuration _
        split <;> simp_all
      _ = _ := by rw [Finset.sum_sub_distrib, sum_bernoulliWeight]; rfl
  have hfailure : (∑ configuration : Fin outerEdges → Configuration innerEdges,
      (∏ edge, bernoulliWeight p (configuration edge)) *
        ∑ edge : Fin outerEdges, if S.crosses (configuration edge) then (0 : ℝ) else 1) =
      (outerEdges : ℝ) * (1 - S.reliability p) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    have hedge (edge : Fin outerEdges) :
        (∑ configuration : Fin outerEdges → Configuration innerEdges,
          (∏ e, bernoulliWeight p (configuration e)) *
            (if S.crosses (configuration edge) then (0 : ℝ) else 1)) = 1 - S.reliability p := by
      rw [finite_product_local_moment
        (fun (_ : Fin outerEdges) cell => bernoulliWeight p cell)
        (fun cell => if S.crosses cell then (0 : ℝ) else 1) edge]
      simp only [sum_bernoulliWeight, Finset.prod_const_one, one_mul, hlocal]
    simp only [hedge, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold expectedBirthClusterPower
  rw [← substitutionConfigurationEquiv.sum_comp, ← substitutionConfigurationEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, bernoulliWeight_substitutionConfiguration]
  have hb := finite_random_family_rare_square
    (fun configuration : Fin outerEdges → Configuration innerEdges => ∏ e, bernoulliWeight p (configuration e))
    (fun configuration => ∑ e : Fin outerEdges, if S.crosses (configuration e) then (0 : ℝ) else 1)
    (R.birthClusterFamily S) (fun _ cluster => (cluster.card : ℝ) ^ order) outerVertices
    (fun _ => Finset.prod_nonneg (fun _ _ => bernoulliWeight_nonneg hp hp' _))
    (fun _ => Finset.sum_nonneg (fun _ _ => by split <;> norm_num))
    (R.birthClusterFamily_card_le_vertices S)
    (by
      intro configuration hnonempty
      have hnot : ¬ ∀ edge, S.crosses (configuration edge) = true := by
        intro hall
        simpa only [R.birthClusterFamily_eq_empty_of_all_cross S hconnected configuration hall,
          Finset.not_nonempty_empty] using hnonempty
      push Not at hnot
      obtain ⟨edge, hedge⟩ := hnot
      have hs := Finset.single_le_sum (s := Finset.univ)
        (f := fun e : Fin outerEdges => if S.crosses (configuration e) then (0 : ℝ) else 1)
        (fun e _ => by split <;> norm_num) (Finset.mem_univ edge)
      simpa only [hedge, Bool.false_eq_true, ↓reduceIte] using hs)
  rw [hfailure] at hb
  simpa only [← pow_mul, Nat.mul_comm order 2] using hb

end
end Universality.FiniteNetwork
