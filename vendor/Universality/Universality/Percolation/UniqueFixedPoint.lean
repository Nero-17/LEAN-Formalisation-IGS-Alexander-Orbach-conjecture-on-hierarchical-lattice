import Universality.Percolation.StrictInstability
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

namespace Universality
noncomputable section

def probabilityLogOdds (p : ℝ) : ℝ := Real.log p - Real.log (1 - p)

theorem probabilityLogOdds_strictMonoOn : StrictMonoOn probabilityLogOdds (Set.Ioo 0 1) := by
  intro p hp q hq hpq
  have hfirst := Real.log_lt_log hp.1 hpq
  have hsecond := Real.log_lt_log (sub_pos.mpr hq.2) (by linarith : 1 - q < 1 - p)
  unfold probabilityLogOdds
  linarith

theorem probabilityLogOdds_hasDerivAt {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    HasDerivAt probabilityLogOdds (1 / (p * (1 - p))) p := by
  change HasDerivAt (fun x : ℝ => Real.log x - Real.log (1 - x)) _ p
  have h := (Real.hasDerivAt_log hp.ne').sub
    (((hasDerivAt_id p).const_sub 1).log (sub_pos.mpr hp').ne')
  convert! h using 1
  simp only [id_eq]
  field_simp [hp.ne', (sub_pos.mpr hp').ne']
  ring

namespace FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem reliability_lt_one {p : ℝ} (hp : 0 < p) (hp' : p < 1) :
    R.reliability p < 1 := by
  conv_rhs => rw [← sum_bernoulliWeight (edges := edges) p]
  unfold reliability
  apply Finset.sum_lt_sum
  · intro ω _
    split
    · exact le_rfl
    · exact (bernoulliWeight_pos hp hp' ω).le
  · refine ⟨fun _ => false, Finset.mem_univ _, ?_⟩
    simp only [R.crosses_all_closed, Bool.false_eq_true, ↓reduceIte]
    exact bernoulliWeight_pos hp hp' _

def logOddsDifference (p : ℝ) : ℝ := probabilityLogOdds (R.reliability p) - probabilityLogOdds p

theorem logOddsDifference_hasDerivAt (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target) :
    HasDerivAt R.logOddsDifference
      ((p * (1 - p) * deriv R.reliability p - R.reliability p * (1 - R.reliability p)) /
        (p * (1 - p) * (R.reliability p * (1 - R.reliability p)))) p := by
  have hpositive := (R.reliability_pos_iff_connected hp hp').mpr hconnected
  have hless := R.reliability_lt_one hp hp'
  have hderivative := (R.hasDerivAt_reliability p).differentiableAt.hasDerivAt
  have h := ((probabilityLogOdds_hasDerivAt hpositive hless).comp p hderivative).sub
    (probabilityLogOdds_hasDerivAt hp hp')
  change HasDerivAt R.logOddsDifference
    ((1 / (R.reliability p * (1 - R.reliability p))) * deriv R.reliability p -
      1 / (p * (1 - p))) p at h
  convert h using 1
  field_simp [hp.ne', (sub_pos.mpr hp').ne', hpositive.ne', (sub_pos.mpr hless).ne']

theorem logOddsDifference_strictMonoOn
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target) :
    StrictMonoOn R.logOddsDifference (Set.Ioo 0 1) := by
  apply strictMonoOn_of_deriv_pos (convex_Ioo 0 1)
  · intro p hp
    exact (R.logOddsDifference_hasDerivAt p hp.1 hp.2 hconnected).continuousAt.continuousWithinAt
  · intro p hp
    rw [interior_Ioo] at hp
    rw [(R.logOddsDifference_hasDerivAt p hp.1 hp.2 hconnected).deriv]
    apply div_pos
    · exact sub_pos.mpr (R.strict_crossing_differential_inequality p hp.1 hp.2 hconnected hscale)
    · exact mul_pos (mul_pos hp.1 (sub_pos.mpr hp.2))
        (mul_pos ((R.reliability_pos_iff_connected hp.1 hp.2).mpr hconnected)
          (sub_pos.mpr (R.reliability_lt_one hp.1 hp.2)))

theorem interior_fixed_point_unique (p q : ℝ)
    (hp : 0 < p) (hp' : p < 1) (hq : 0 < q) (hq' : q < 1)
    (hfixedp : R.reliability p = p) (hfixedq : R.reliability q = q)
    (hscale : 1 < R.fullGraph.dist R.source R.target) : p = q := by
  have hconnected := (R.reliability_pos_iff_connected hp hp').mp (by rwa [hfixedp])
  apply (R.logOddsDifference_strictMonoOn hconnected hscale).injOn ⟨hp, hp'⟩ ⟨hq, hq'⟩
  simp [logOddsDifference, hfixedp, hfixedq]

theorem reliability_lt_parameter_below_fixed (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : R.reliability critical = critical)
    (hp : 0 < p) (hpc : p < critical)
    (hscale : 1 < R.fullGraph.dist R.source R.target) : R.reliability p < p := by
  have hp' := hpc.trans hc'
  have hconnected := (R.reliability_pos_iff_connected hc hc').mp (by rwa [hfixed])
  have h := R.logOddsDifference_strictMonoOn hconnected hscale ⟨hp, hp'⟩ ⟨hc, hc'⟩ hpc
  simp only [logOddsDifference, hfixed, sub_self] at h
  by_contra hnot
  have hmon := probabilityLogOdds_strictMonoOn.monotoneOn ⟨hp, hp'⟩
    ⟨(R.reliability_pos_iff_connected hp hp').mpr hconnected, R.reliability_lt_one hp hp'⟩
    (le_of_not_gt hnot)
  linarith

theorem parameter_lt_reliability_above_fixed (critical p : ℝ)
    (hc : 0 < critical) (hc' : critical < 1) (hfixed : R.reliability critical = critical)
    (hpc : critical < p) (hp' : p < 1)
    (hscale : 1 < R.fullGraph.dist R.source R.target) : p < R.reliability p := by
  have hp := hc.trans hpc
  have hconnected := (R.reliability_pos_iff_connected hc hc').mp (by rwa [hfixed])
  have h := R.logOddsDifference_strictMonoOn hconnected hscale ⟨hc, hc'⟩ ⟨hp, hp'⟩ hpc
  simp only [logOddsDifference, hfixed, sub_self] at h
  by_contra hnot
  have hmon := probabilityLogOdds_strictMonoOn.monotoneOn
    ⟨(R.reliability_pos_iff_connected hp hp').mpr hconnected, R.reliability_lt_one hp hp'⟩
    ⟨hp, hp'⟩ (le_of_not_gt hnot)
  linarith

end FiniteNetwork
end
end Universality
