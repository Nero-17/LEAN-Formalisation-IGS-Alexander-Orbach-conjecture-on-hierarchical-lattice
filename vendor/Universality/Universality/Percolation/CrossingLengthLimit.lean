import Universality.Analysis.NormalizedLogIteration
import Universality.Percolation.CrossingPowerBounds
import Universality.Percolation.ClassicalCriticalPoint

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem reliability_log_correction_bound (p upper : ℝ) (hp : 0 < p) (hpu : p ≤ upper) (hu : upper < 1)
    (hsimple : Function.Injective (fun edge => s((R.endpoint edge).1, (R.endpoint edge).2)))
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    |Real.log (R.reliability p) - (R.fullGraph.dist R.source R.target : ℝ) * Real.log p| ≤
      |Real.log ((1 - upper) ^ edges)| + |Real.log ((2 : ℝ) ^ edges)| := by
  have hratio := R.reliability_distance_ratio_bounds p upper hp hpu hu hsimple hconnected
  have hlower : 0 < (1 - upper) ^ edges := pow_pos (sub_pos.mpr hu) edges
  have hpositive : 0 < R.reliability p := (R.reliability_pos_iff_connected hp (hpu.trans_lt hu)).mpr hconnected
  have hidentity : Real.log (R.reliability p / p ^ R.fullGraph.dist R.source R.target) =
      Real.log (R.reliability p) - (R.fullGraph.dist R.source R.target : ℝ) * Real.log p := by
    rw [Real.log_div hpositive.ne' (pow_ne_zero _ hp.ne'), Real.log_pow]
  rw [← hidentity]
  have hlowlog := Real.log_le_log hlower hratio.1
  have hhighlog := Real.log_le_log (hlower.trans_le hratio.1) hratio.2
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log ((1 - upper) ^ edges)), abs_nonneg (Real.log ((2 : ℝ) ^ edges))]
  · linarith [le_abs_self (Real.log ((2 : ℝ) ^ edges)), abs_nonneg (Real.log ((1 - upper) ^ edges))]

theorem subcritical_reliability_orbit_bounds (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : R.reliability critical = critical)
    (hp : 0 < p) (hpc : p < critical)
    (hscale : 1 < R.fullGraph.dist R.source R.target)
    (hconnected : R.fullGraph.Reachable R.source R.target) (n : ℕ) :
    0 < R.reliability^[n] p ∧ R.reliability^[n] p ≤ p := by
  induction n with
  | zero => exact ⟨hp, le_rfl⟩
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact ⟨(R.reliability_pos_iff_connected ih.1 (ih.2.trans_lt (hpc.trans hc'))).mpr hconnected,
      (R.reliability_le_parameter_below_fixed critical _ hc hc' hfixed ih.1.le (ih.2.trans_lt hpc) hscale).trans ih.2⟩

/-- Defined by the logarithmic correction series; the subsequent theorem
identifies it with the actual iterated-crossing limit. -/
def inverseCrossingLength (p : ℝ) : ℝ :=
  -normalizedLogLimit (fun n => R.reliability^[n] p) (R.fullGraph.dist R.source R.target : ℝ)

def crossingCorrelationLength (p : ℝ) : ℝ := 1 / R.inverseCrossingLength p

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
set_option maxHeartbeats 0
open Filter FiniteNetwork
open scoped Topology

theorem Classical.subcritical_log_correction_bound {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) (n : ℕ) :
    |Real.log (rule.network.reliability^[n + 1] p) -
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) * Real.log (rule.network.reliability^[n] p)| ≤
      |Real.log ((1 - critical) ^ rule.edges)| + |Real.log ((2 : ℝ) ^ rule.edges)| := by
  have hbounds := rule.network.subcritical_reliability_orbit_bounds critical p hc hc' hfixed hp hpc h.scale (h.connected _) n
  rw [Function.iterate_succ_apply']
  exact rule.network.reliability_log_correction_bound _ critical hbounds.1 (hbounds.2.trans hpc.le) hc' h.simple (h.connected _)

theorem Classical.crossing_length_limit {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    0 < rule.network.inverseCrossingLength p ∧
      Tendsto (fun n : ℕ => -Real.log (rule.network.reliability^[n] p) /
        (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ n) atTop
        (𝓝 (rule.network.inverseCrossingLength p)) := by
  have hscale : (1 : ℝ) < rule.network.fullGraph.dist rule.network.source rule.network.target := by exact_mod_cast h.scale
  have hbound := h.subcritical_log_correction_bound critical p hc hc' hfixed hp hpc
  constructor
  · apply neg_pos.mpr
    apply normalizedLogLimit_neg _ _ _ hscale hbound
    · intro n
      exact (rule.network.subcritical_reliability_orbit_bounds critical p hc hc' hfixed hp hpc h.scale (h.connected _) n).1
    · exact rule.network.iterate_reliability_tendsto_zero critical p hc hc' hfixed hp.le hpc h.scale
  · simpa only [inverseCrossingLength, neg_div] using
      (tendsto_normalized_log _ _ _ hscale hbound).neg

theorem Classical.crossingCorrelationLength_pos {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    0 < rule.network.crossingCorrelationLength p :=
  one_div_pos.mpr (h.crossing_length_limit critical p hc hc' hfixed hp hpc).1

end
end Universality.Rule
