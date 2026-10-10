import Universality.Percolation.ClusterNumberSecondDerivativeEquation
import Universality.Analysis.PuncturedDerivativeExtension
import Mathlib.Topology.Piecewise

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter Set
open scoped Topology ContDiff

theorem Classical.cluster_number_second_deriv_continuousAt_critical {rule : Rule}
    (h : rule.Classical) (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    DifferentiableAt ℝ (deriv rule.network.clusterNumberAnalyticExtension) critical ∧
      ContinuousAt (deriv (deriv rule.network.clusterNumberAnalyticExtension)) critical := by
  let center : Icc (0 : ℝ) 1 := ⟨critical, hc.le, hc'.le⟩
  let crossing : Polynomial ℝ := rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)
  let forcing : Polynomial ℝ := rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)
  let normalization : ℝ := ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)
  have hcrossing (p : ℝ) : crossing.derivative.eval p = deriv rule.network.reliability p := by
    dsimp [crossing]
    rw [Polynomial.derivative_map, Polynomial.eval_map, (rule.network.hasDerivAt_reliability p).deriv]
  have hsquare : crossing.derivative.eval critical ^ 2 < (rule.edges : ℝ) := by
    rw [hcrossing]
    exact rule.network.pivotal_response_sq_lt_edges critical hc hc' hfixed h.scale
  have hmass : (0 : ℝ) < rule.edges := lt_of_le_of_lt (sq_nonneg _) hsquare
  let second := (crossing.derivative.derivative.eval critical *
      deriv rule.network.clusterNumberAnalyticExtension critical +
      normalization * forcing.derivative.derivative.eval critical) /
    ((rule.edges : ℝ) - crossing.derivative.eval critical ^ 2)
  have hsecond : (rule.edges : ℝ) * second = crossing.derivative.eval critical ^ 2 * second +
      crossing.derivative.derivative.eval critical * deriv rule.network.clusterNumberAnalyticExtension critical +
        normalization * forcing.derivative.derivative.eval critical := by
    have hgap : (rule.edges : ℝ) - crossing.derivative.eval critical ^ 2 ≠ 0 :=
      (sub_pos.mpr hsquare).ne'
    have heq : second * ((rule.edges : ℝ) - crossing.derivative.eval critical ^ 2) =
        crossing.derivative.derivative.eval critical * deriv rule.network.clusterNumberAnalyticExtension critical +
          normalization * forcing.derivative.derivative.eval critical := (eq_div_iff hgap).mp rfl
    nlinarith
  let response := Function.update (deriv (deriv rule.network.clusterNumberAnalyticExtension)) critical second
  have hresponseCenter : response critical = second := Function.update_self ..
  have hfirst := h.cluster_number_deriv_continuousAt_critical critical hc hc' hfixed
  have hfirstAt : ContinuousAt (deriv rule.network.clusterNumberAnalyticExtension)
      (rule.network.reliability critical) := by simpa only [hfixed] using hfirst
  have hnextFirst : ContinuousAt
      (fun p => deriv rule.network.clusterNumberAnalyticExtension (rule.network.reliability p)) critical :=
    hfirstAt.comp (rule.network.hasDerivAt_reliability critical).continuousAt
  obtain ⟨radius, hradius, hescape⟩ := h.unitReliability_escape critical hc hc' hfixed
  have hcontinuous : ContinuousAt (fun p : Icc (0 : ℝ) 1 => response p.val) center := by
    apply continuousAt_of_compact_renormalization rule.network.unitReliability
      (fun p => response p.val)
      (fun p => crossing.derivative.eval p.val ^ 2 / (rule.edges : ℝ))
      (fun p => (crossing.derivative.derivative.eval p.val *
          deriv rule.network.clusterNumberAnalyticExtension (rule.network.reliability p.val) +
        normalization * forcing.derivative.derivative.eval p.val) / (rule.edges : ℝ))
      center radius hradius rule.network.continuous_unitReliability.continuousAt (Subtype.ext hfixed)
      hescape
    · intro p hp
      have hne : p.val ≠ critical := by
        intro heq
        exact hp (Set.mem_singleton_iff.mpr (Subtype.ext heq))
      have hanalytic := (h.cluster_number_analyticAt_offcritical critical p.val hc hc' hfixed
        p.property.1 p.property.2 hne).deriv.deriv
      exact (((continuousAt_update_of_ne hne).mpr hanalytic.continuousAt).comp
        continuous_subtype_val.continuousAt).continuousWithinAt
    · exact ((crossing.derivative.continuous.comp continuous_subtype_val).pow 2).continuousAt.div_const _
    · have hforcingContinuous : ContinuousAt (fun p : ℝ =>
          (crossing.derivative.derivative.eval p *
            deriv rule.network.clusterNumberAnalyticExtension (rule.network.reliability p) +
              normalization * forcing.derivative.derivative.eval p) / (rule.edges : ℝ)) critical :=
          ((crossing.derivative.derivative.continuous.continuousAt.mul hnextFirst).add
            (continuousAt_const.mul forcing.derivative.derivative.continuous.continuousAt)).div_const _
      exact hforcingContinuous.comp (continuousAt_subtype_val (x := center))
    · change |crossing.derivative.eval critical ^ 2 / (rule.edges : ℝ)| < 1
      rw [abs_of_nonneg (div_nonneg (sq_nonneg _) hmass.le)]
      exact (div_lt_one hmass).mpr hsquare
    · have hinterior : ∀ᶠ p : Icc (0 : ℝ) 1 in 𝓝 center, p.val ∈ Ioo (0 : ℝ) 1 :=
        continuous_subtype_val.continuousAt.eventually (Ioo_mem_nhds hc hc')
      filter_upwards [hinterior] with p hp
      by_cases heq : p.val = critical
      · change response p.val = crossing.derivative.eval p.val ^ 2 / (rule.edges : ℝ) *
          response (rule.network.reliability p.val) + _
        simp only [heq, hfixed, hresponseCenter]
        rw [div_mul_eq_mul_div, ← add_div]
        apply (eq_div_iff hmass.ne').mpr
        nlinarith [hsecond]
      · have hneNext := h.reliability_ne_critical critical p.val hc hc' hfixed hp.1.le hp.2.le heq
        have hequation := h.cluster_number_second_deriv_equation critical p.val hc hc' hfixed hp.1 hp.2 heq
        change response p.val = crossing.derivative.eval p.val ^ 2 / (rule.edges : ℝ) *
          response (rule.network.reliability p.val) + _
        simp only [response, Function.update_of_ne heq, Function.update_of_ne hneNext]
        dsimp [crossing, forcing, normalization]
        rw [div_mul_eq_mul_div, ← add_div]
        apply (eq_div_iff hmass.ne').mpr
        nlinarith [hequation]
  have hcontinuousReal : ContinuousAt response critical :=
    ((continuousWithinAt_iff_continuousAt_restrict response center.property).mpr
      hcontinuous).continuousAt (Icc_mem_nhds hc hc')
  have hlimit : Tendsto (deriv (deriv rule.network.clusterNumberAnalyticExtension))
      (𝓝[≠] critical) (𝓝 second) := continuousAt_update_same.mp hcontinuousReal
  have hhasDeriv : HasDerivAt (deriv rule.network.clusterNumberAnalyticExtension) second critical := by
    apply hasDerivAt_of_punctured_derivative_limit _ _ critical second hfirst ?_ hlimit
    filter_upwards [nhdsWithin_le_nhds (Ioo_mem_nhds hc hc'), self_mem_nhdsWithin] with p hp hne
    exact (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.1.le hp.2.le hne).deriv.differentiableAt.hasDerivAt
  refine ⟨hhasDeriv.differentiableAt, ?_⟩
  have heq : response = deriv (deriv rule.network.clusterNumberAnalyticExtension) := by
    funext p
    by_cases hp : p = critical
    · subst p
      exact hresponseCenter.trans hhasDeriv.deriv.symm
    exact Function.update_of_ne hp ..
  rwa [heq] at hcontinuousReal

theorem Classical.cluster_number_contDiffOn_two {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ContDiffOn ℝ 2 rule.network.clusterNumberAnalyticExtension (Ioo (0 : ℝ) 1) := by
  have hsecond := h.cluster_number_second_deriv_continuousAt_critical critical hc hc' hfixed
  rw [show (2 : ℕ∞ω) = 1 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, by simp, ?_⟩
  · intro p hp
    exact (h.cluster_number_differentiableAt critical p hc hc' hfixed hp.1.le hp.2.le).differentiableWithinAt
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, by simp, ?_⟩
  · intro p hp
    by_cases heq : p = critical
    · subst p
      exact hsecond.1.differentiableWithinAt
    exact (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.1.le hp.2.le heq).deriv.differentiableAt.differentiableWithinAt
  rw [contDiffOn_zero]
  intro p hp
  by_cases heq : p = critical
  · subst p
    exact hsecond.2.continuousWithinAt
  exact (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.1.le hp.2.le heq).deriv.deriv.continuousAt.continuousWithinAt

end
end Universality.Rule

