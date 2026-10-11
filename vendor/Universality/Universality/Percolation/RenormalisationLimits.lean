import Universality.Percolation.UniqueFixedPoint
import Universality.Graph.Iteration
import Mathlib.Dynamics.FixedPoints.Topology
import Mathlib.Topology.Order.MonotoneConvergence

namespace Universality.FiniteNetwork
noncomputable section
open Filter
open scoped Topology

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem reliability_le_parameter_below_fixed (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : R.reliability critical = critical)
    (hp : 0 ≤ p) (hpc : p < critical)
    (hscale : 1 < R.fullGraph.dist R.source R.target) : R.reliability p ≤ p := by
  rcases hp.eq_or_lt with h | h
  · subst p
    rw [R.reliability_zero]
  · exact (R.reliability_lt_parameter_below_fixed critical p hc hc' hfixed h hpc hscale).le

theorem parameter_le_reliability_above_fixed (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : R.reliability critical = critical)
    (hpc : critical < p) (hp' : p ≤ 1)
    (hscale : 1 < R.fullGraph.dist R.source R.target) : p ≤ R.reliability p := by
  rcases hp'.lt_or_eq with h | h
  · exact (R.parameter_lt_reliability_above_fixed critical p hc hc' hfixed hpc h hscale).le
  · subst p
    have hconnected := (R.reliability_pos_iff_connected hc hc').mp (by rwa [hfixed])
    rw [R.reliability_one hconnected]

theorem iterate_reliability_tendsto_zero (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : R.reliability critical = critical)
    (hp : 0 ≤ p) (hpc : p < critical)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    Tendsto (fun n : ℕ => R.reliability^[n] p) atTop (𝓝 0) := by
  have hbounds : ∀ n : ℕ, 0 ≤ R.reliability^[n] p ∧ R.reliability^[n] p ≤ p := by
    intro n
    induction n with
    | zero => exact ⟨hp, le_rfl⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨R.reliability_nonneg ih.1 ((ih.2.trans_lt (hpc.trans hc')).le),
        (R.reliability_le_parameter_below_fixed critical _ hc hc' hfixed ih.1
          (ih.2.trans_lt hpc) hscale).trans ih.2⟩
  have hanti : Antitone (fun n : ℕ => R.reliability^[n] p) := by
    apply antitone_nat_of_succ_le
    intro n
    rw [Function.iterate_succ_apply']
    exact R.reliability_le_parameter_below_fixed critical _ hc hc' hfixed (hbounds n).1
      ((hbounds n).2.trans_lt hpc) hscale
  have hbounded : BddBelow (Set.range (fun n : ℕ => R.reliability^[n] p)) :=
    ⟨0, by rintro _ ⟨n, rfl⟩; exact (hbounds n).1⟩
  have hlimit := tendsto_atTop_ciInf hanti hbounded
  have hlower : 0 ≤ ⨅ n : ℕ, R.reliability^[n] p := le_ciInf (fun n => (hbounds n).1)
  have hupper : (⨅ n : ℕ, R.reliability^[n] p) ≤ p := ciInf_le hbounded 0
  have hlimitfixed := isFixedPt_of_tendsto_iterate hlimit
    (R.hasDerivAt_reliability _).continuousAt
  have hzero : (⨅ n : ℕ, R.reliability^[n] p) = 0 := by
    by_contra h
    have hpositive := lt_of_le_of_ne hlower (Ne.symm h)
    have heq := R.interior_fixed_point_unique _ critical hpositive
      (hupper.trans_lt (hpc.trans hc')) hc hc' hlimitfixed hfixed hscale
    have hless := hupper.trans_lt hpc
    rw [heq] at hless
    exact lt_irrefl _ hless
  rwa [hzero] at hlimit

theorem iterate_reliability_tendsto_one (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : R.reliability critical = critical)
    (hpc : critical < p) (hp' : p ≤ 1)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    Tendsto (fun n : ℕ => R.reliability^[n] p) atTop (𝓝 1) := by
  have hbounds : ∀ n : ℕ, p ≤ R.reliability^[n] p ∧ R.reliability^[n] p ≤ 1 := by
    intro n
    induction n with
    | zero => exact ⟨le_rfl, hp'⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨ih.1.trans (R.parameter_le_reliability_above_fixed critical _ hc hc' hfixed
        (hpc.trans_le ih.1) ih.2 hscale),
        R.reliability_le_one ((hc.trans hpc).le.trans ih.1) ih.2⟩
  have hmono : Monotone (fun n : ℕ => R.reliability^[n] p) := by
    apply monotone_nat_of_le_succ
    intro n
    rw [Function.iterate_succ_apply']
    exact R.parameter_le_reliability_above_fixed critical _ hc hc' hfixed
      (hpc.trans_le (hbounds n).1) (hbounds n).2 hscale
  have hbounded : BddAbove (Set.range (fun n : ℕ => R.reliability^[n] p)) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (hbounds n).2⟩
  have hlimit := tendsto_atTop_ciSup hmono hbounded
  have hlower : p ≤ ⨆ n : ℕ, R.reliability^[n] p := le_ciSup hbounded 0
  have hupper : (⨆ n : ℕ, R.reliability^[n] p) ≤ 1 := ciSup_le (fun n => (hbounds n).2)
  have hlimitfixed := isFixedPt_of_tendsto_iterate hlimit
    (R.hasDerivAt_reliability _).continuousAt
  have hone : (⨆ n : ℕ, R.reliability^[n] p) = 1 := by
    by_contra h
    have hless := lt_of_le_of_ne hupper h
    have heq := R.interior_fixed_point_unique _ critical ((hc.trans hpc).trans_le hlower)
      hless hc hc' hlimitfixed hfixed hscale
    have hgreater := hpc.trans_le hlower
    rw [heq] at hgreater
    exact lt_irrefl _ hgreater
  rwa [hone] at hlimit

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem generation_reliability_iterate (rule : Rule) (n : ℕ) (p : ℝ) :
    (rule.generation n).network.reliability p = rule.network.reliability^[n + 1] p := by
  induction n generalizing p with
  | zero => simp [generation]
  | succ n ih =>
    rw [generation, mul_reliability, ih]
    exact (Function.iterate_succ_apply rule.network.reliability (n + 1) p).symm

theorem generation_crossing_tendsto_zero (rule : Rule) (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : rule.network.reliability critical = critical)
    (hp : 0 ≤ p) (hpc : p < critical)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    Tendsto (fun n : ℕ => (rule.generation n).network.reliability p) atTop (𝓝 0) := by
  have h := (rule.network.iterate_reliability_tendsto_zero critical p hc hc' hfixed hp hpc hscale).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, rule.generation_reliability_iterate] using h

theorem generation_crossing_tendsto_one (rule : Rule) (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : rule.network.reliability critical = critical)
    (hpc : critical < p) (hp' : p ≤ 1)
    (hscale : 1 < rule.network.fullGraph.dist rule.network.source rule.network.target) :
    Tendsto (fun n : ℕ => (rule.generation n).network.reliability p) atTop (𝓝 1) := by
  have h := (rule.network.iterate_reliability_tendsto_one critical p hc hc' hfixed hpc hp' hscale).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, rule.generation_reliability_iterate] using h

end
end Universality.Rule
