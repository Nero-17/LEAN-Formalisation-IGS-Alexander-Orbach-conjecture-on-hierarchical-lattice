import Universality.Percolation.SubcriticalBoundaryMomentBound
import Universality.Percolation.Russo
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ}

theorem expectation_monotoneOn_of_resampling (response : Configuration edges → ℝ)
    (hresponse : ∀ configuration edge, response (Function.update configuration edge false) ≤
      response (Function.update configuration edge true)) :
    MonotoneOn (fun p => expectation p response) (Set.Icc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc 0 1)
  · intro p _
    exact (hasDerivAt_expectation response p).continuousAt.continuousWithinAt
  · intro p _
    exact (hasDerivAt_expectation response p).differentiableAt.differentiableWithinAt
  · intro p hp
    rw [interior_Icc] at hp
    rw [(hasDerivAt_expectation_resampling response p).deriv]
    apply Finset.sum_nonneg
    intro edge _
    exact Finset.sum_nonneg (fun configuration _ =>
      mul_nonneg (bernoulliWeight_nonneg hp.1.le hp.2.le _) (sub_nonneg.mpr (hresponse configuration edge)))

theorem reliability_monotoneOn (R : FiniteNetwork vertices edges) :
    MonotoneOn R.reliability (Set.Icc 0 1) := by
  have hmono := expectation_monotoneOn_of_resampling R.crossingIndicator (by
    intro configuration edge
    have hdiff := R.crossingIndicator_difference configuration edge
    have hnonneg : (0 : ℝ) ≤ if R.pivotal configuration edge then 1 else 0 := by split <;> norm_num
    rw [← hdiff] at hnonneg
    exact sub_nonneg.mp hnonneg)
  simpa only [R.expectation_crossingIndicator] using hmono

theorem internalSelectedMass_mono_configuration (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (first second : Configuration edges)
    (hopen : ∀ edge, first edge = true → second edge = true) :
    R.internalSelectedMass sourceSelected targetSelected first ≤
      R.internalSelectedMass sourceSelected targetSelected second := by
  have hgraph : R.openGraph first ≤ R.openGraph second := by
    intro u v hadj
    obtain ⟨hne, edge, he, hpair⟩ := hadj
    exact ⟨hne, edge, hopen edge he, hpair⟩
  have hactive (vertex : Fin vertices) : R.selectedActive sourceSelected targetSelected first vertex = true →
      R.selectedActive sourceSelected targetSelected second vertex = true := by
    simp only [selectedActive, Bool.or_eq_true, Bool.and_eq_true,
      SimpleGraph.reachableDecide_eq_true]
    intro hvertex
    exact hvertex.elim (fun h => Or.inl ⟨h.1, h.2.mono hgraph⟩)
      (fun h => Or.inr ⟨h.1, h.2.mono hgraph⟩)
  unfold internalSelectedMass
  apply Finset.sum_le_sum
  intro vertex _
  by_cases hfirst : R.selectedActive sourceSelected targetSelected first vertex.val = true
  · simp only [hfirst, hactive vertex.val hfirst, ↓reduceIte, le_refl]
  · simp only [hfirst, ↓reduceIte]
    exact Nat.zero_le _

theorem expectedInternalBoundaryMoment_monotoneOn (R : FiniteNetwork vertices edges) (order : ℕ) :
    MonotoneOn (fun p => R.expectedInternalBoundaryMoment p order) (Set.Icc 0 1) := by
  apply expectation_monotoneOn_of_resampling
    (fun configuration => (R.internalSelectedMass true true configuration : ℝ) ^ order)
  intro configuration edge
  apply pow_le_pow_left₀ (Nat.cast_nonneg _)
  exact_mod_cast R.internalSelectedMass_mono_configuration true true
    (Function.update configuration edge false) (Function.update configuration edge true)
    (by
      intro other hopen
      by_cases heq : other = edge
      · subst other
        simp
      · simpa only [Function.update_of_ne heq] using hopen)

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section

theorem Classical.subcritical_boundary_moment_uniform_bound {rule : Rule} (h : rule.Classical)
    (critical upperParameter : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hu : 0 ≤ upperParameter)
    (huc : upperParameter < critical) (order : ℕ) (horder : 1 ≤ order) :
    ∃ bound : ℝ, 0 < bound ∧ ∀ p, 0 ≤ p → p ≤ upperParameter → ∀ n,
      (rule.generation n).network.expectedInternalBoundaryMoment p order ≤
        bound * (rule.network.fullGraph.degree rule.network.source : ℝ) ^ (order * n) := by
  obtain ⟨bound, hbound, hb⟩ := h.subcritical_boundary_moment_bound critical upperParameter hc hc' hfixed hu huc order horder
  refine ⟨bound, hbound, ?_⟩
  intro p hp hpu n
  exact ((rule.generation n).network.expectedInternalBoundaryMoment_monotoneOn order
    ⟨hp, hpu.trans (huc.trans hc').le⟩ ⟨hu, (huc.trans hc').le⟩ hpu).trans (hb n)

end
end Universality.Rule
