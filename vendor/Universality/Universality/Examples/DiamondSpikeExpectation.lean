import Universality.Examples.DiamondSpikeFiniteEvent
import Universality.Percolation.NestedConfigurationLaw

namespace Universality.FiniteNetwork
noncomputable section
open scoped BigOperators
set_option maxHeartbeats 800000

theorem triple_crossing_coefficient {edges : ℕ} (q : ℝ) (coarse : Configuration edges) :
    (∏ edge, ∏ _ : Fin 4, ∏ _ : Fin 4, (if coarse edge then q else 1 - q)) =
      bernoulliWeight q coarse ^ 16 := by
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rw [Finset.prod_pow]
  rfl

end
end Universality.FiniteNetwork

namespace Universality
noncomputable section
open FiniteNetwork
open scoped BigOperators
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {outerVertices outerEdges vertices edges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork vertices edges)

theorem diamond_spike_expectation
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (hconnected : ∀ vertex, S.fullGraph.Reachable S.source vertex)
    (hlayers : ∀ vertex, S.fullGraph.dist S.source vertex + S.fullGraph.dist vertex S.target =
      S.fullGraph.dist S.source S.target)
    (hdiameter : ∀ u v, S.fullGraph.dist u v ≤ S.fullGraph.dist S.source S.target)
    (hpositiveLength : 0 < S.fullGraph.dist S.source S.target)
    (hgeodesic : ∀ configuration, S.crosses configuration = true →
      ∃ walk : (S.openGraph configuration).Walk S.source S.target,
        walk.length = S.fullGraph.dist S.source S.target)
    (mainEdge : Fin outerEdges)
    (hfirstSource : (R.endpoint mainEdge).1 ≠ R.source)
    (hfirstTarget : (R.endpoint mainEdge).1 ≠ R.target)
    (hsecondSource : (R.endpoint mainEdge).2 ≠ R.source)
    (hsecondTarget : (R.endpoint mainEdge).2 ≠ R.target)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1) :
    bernoulliWeight (S.reliability p) (onlyOpen mainEdge) ^ 16 * S.conditionalVertexMass p .connected ≤
      (R.substitute (diamondNetwork.substitute (diamondNetwork.substitute S))).expectedInternalRadiusPointRootCount
        p (4 * S.fullGraph.dist S.source S.target) := by
  classical
  let coefficient := bernoulliWeight (S.reliability p) (onlyOpen mainEdge) ^ 16
  let kernel (cells : Fin outerEdges → Fin 4 → Fin 4 → Configuration edges) : ℝ :=
    ∏ edge, ∏ first, ∏ second, S.conditionalCellWeight p (onlyOpen mainEdge edge) (cells edge first second)
  let count (cells : Fin outerEdges → Fin 4 → Fin 4 → Configuration edges) : ℝ :=
    (R.substitute (diamondNetwork.substitute (diamondNetwork.substitute S))).internalRadiusPointRootCount
      (tripleConfigurationEquiv cells) (4 * S.fullGraph.dist S.source S.target)
  have hkernelNonneg (cells) : 0 ≤ kernel cells :=
    Finset.prod_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ => Finset.prod_nonneg
      (fun _ _ => S.conditionalCellWeight_nonneg hp hp' _ _)))
  have hcoefficientNonneg : 0 ≤ coefficient := pow_nonneg (bernoulliWeight_nonneg hpositive.le hless.le _) _
  have hqNonneg (edge : Fin outerEdges) :
      0 ≤ (if onlyOpen mainEdge edge then S.reliability p else 1 - S.reliability p) := by
    split
    · exact hpositive.le
    · exact sub_nonneg.mpr hless.le
  have hdomination (cells) : coefficient * kernel cells ≤ bernoulliWeight p (tripleConfigurationEquiv cells) := by
    have hfactor : coefficient * kernel cells =
        ∏ edge, ∏ first, ∏ second,
          (if onlyOpen mainEdge edge then S.reliability p else 1 - S.reliability p) *
            S.conditionalCellWeight p (onlyOpen mainEdge edge) (cells edge first second) := by
      dsimp only [coefficient, kernel]
      rw [← triple_crossing_coefficient]
      simp only [Finset.prod_mul_distrib]
    rw [hfactor, bernoulliWeight_tripleConfiguration]
    apply Finset.prod_le_prod
    · intro edge _
      exact Finset.prod_nonneg (fun _ _ => Finset.prod_nonneg (fun _ _ =>
        mul_nonneg (hqNonneg edge) (S.conditionalCellWeight_nonneg hp hp' _ _)))
    · intro edge _
      apply Finset.prod_le_prod
      · intro first _
        exact Finset.prod_nonneg (fun _ _ => mul_nonneg (hqNonneg edge) (S.conditionalCellWeight_nonneg hp hp' _ _))
      · intro first _
        apply Finset.prod_le_prod
        · intro second _
          exact mul_nonneg (hqNonneg edge) (S.conditionalCellWeight_nonneg hp hp' _ _)
        · intro second _
          exact S.crossing_probability_mul_conditionalWeight_le hp hp' hpositive hless _ _
  have hpoint (cells) : coefficient * kernel cells * (S.internalSelectedMass true false (cells mainEdge 0 1) : ℝ) ≤
      bernoulliWeight p (tripleConfigurationEquiv cells) * count cells := by
    by_cases hconsistent : ∀ edge first second, S.crosses (cells edge first second) = onlyOpen mainEdge edge
    · have hmass := diamond_spike_finite_event R S houter hconnected hlayers hdiameter hpositiveLength hgeodesic
        mainEdge hfirstSource hfirstTarget hsecondSource hsecondTarget cells
        (fun first second => by simpa [onlyOpen] using hconsistent mainEdge first second)
        (fun edge hedge first second => by simpa [onlyOpen, hedge] using hconsistent edge first second)
      have hmass' : (S.internalSelectedMass true false (cells mainEdge 0 1) : ℝ) ≤ count cells := by
        dsimp only [count]
        rw [tripleConfigurationEquiv_apply]
        exact_mod_cast hmass
      exact (mul_le_mul_of_nonneg_left hmass' (mul_nonneg hcoefficientNonneg (hkernelNonneg cells))).trans
        (mul_le_mul_of_nonneg_right (hdomination cells) (Nat.cast_nonneg _))
    · obtain ⟨edge, hedge⟩ := not_forall.mp hconsistent
      obtain ⟨first, hfirst⟩ := not_forall.mp hedge
      obtain ⟨second, hfailure⟩ := not_forall.mp hfirst
      have hzero : kernel cells = 0 := by
        apply Finset.prod_eq_zero (Finset.mem_univ edge)
        apply Finset.prod_eq_zero (Finset.mem_univ first)
        apply Finset.prod_eq_zero (Finset.mem_univ second)
        simp [conditionalCellWeight, hfailure]
      rw [hzero, mul_zero, zero_mul]
      exact mul_nonneg (bernoulliWeight_nonneg hp hp' _) (Nat.cast_nonneg _)
  have hmean := S.triple_conditional_selected_mass p hpositive hless (onlyOpen mainEdge) mainEdge
    (by simp [onlyOpen])
  change (∑ cells, kernel cells * (S.internalSelectedMass true false (cells mainEdge 0 1) : ℝ)) =
    S.conditionalVertexMass p .connected at hmean
  change coefficient * S.conditionalVertexMass p .connected ≤ _
  rw [← hmean, Finset.mul_sum]
  unfold expectedInternalRadiusPointRootCount
  rw [← tripleConfigurationEquiv.sum_comp]
  apply Finset.sum_le_sum
  intro cells _
  simpa only [mul_assoc] using hpoint cells

end
end Universality


