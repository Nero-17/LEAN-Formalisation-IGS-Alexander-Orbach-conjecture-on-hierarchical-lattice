import Universality.Percolation.ClusterNumberDerivativeEquation
import Mathlib.Analysis.Calculus.ContDiff.Deriv

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter Set
open scoped Topology ContDiff

theorem Classical.cluster_number_deriv_continuousAt_critical {rule : Rule}
    (h : rule.Classical) (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ContinuousAt (deriv rule.network.clusterNumberAnalyticExtension) critical := by
  let center : Icc (0 : ℝ) 1 := ⟨critical, hc.le, hc'.le⟩
  let crossing : Polynomial ℝ := rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)
  let forcing : Polynomial ℝ := rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)
  have hderivative (p : ℝ) : crossing.derivative.eval p = deriv rule.network.reliability p := by
    dsimp [crossing]
    rw [Polynomial.derivative_map, Polynomial.eval_map, (rule.network.hasDerivAt_reliability p).deriv]
  have hrepelling := rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale
  have hsquare := rule.network.pivotal_response_sq_lt_edges critical hc hc' hfixed h.scale
  have hmass : (0 : ℝ) < rule.edges := by nlinarith
  obtain ⟨radius, hradius, hescape⟩ := h.unitReliability_escape critical hc hc' hfixed
  have hcontinuous : ContinuousAt
      (fun p : Icc (0 : ℝ) 1 => deriv rule.network.clusterNumberAnalyticExtension p.val) center := by
    apply continuousAt_of_compact_renormalization rule.network.unitReliability
      (fun p => deriv rule.network.clusterNumberAnalyticExtension p.val)
      (fun p => crossing.derivative.eval p.val / (rule.edges : ℝ))
      (fun p => (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
        forcing.derivative.eval p.val) / (rule.edges : ℝ))
      center radius hradius rule.network.continuous_unitReliability.continuousAt (Subtype.ext hfixed)
      hescape
    · intro p hp
      have hne : p.val ≠ critical := by
        intro heq
        exact hp (Set.mem_singleton_iff.mpr (Subtype.ext heq))
      exact ((h.cluster_number_analyticAt_offcritical critical p.val hc hc' hfixed
        p.property.1 p.property.2 hne).deriv.continuousAt.comp
          continuous_subtype_val.continuousAt).continuousWithinAt
    · exact (crossing.derivative.continuous.comp continuous_subtype_val).continuousAt.div_const _
    · exact ((continuous_const.mul (forcing.derivative.continuous.comp
        continuous_subtype_val)).div_const _).continuousAt
    · change |crossing.derivative.eval critical / (rule.edges : ℝ)| < 1
      rw [hderivative, abs_of_pos (div_pos (by linarith) hmass)]
      exact (div_lt_one hmass).mpr (by nlinarith)
    · have hinterior : ∀ᶠ p : Icc (0 : ℝ) 1 in 𝓝 center, p.val ∈ Ioo (0 : ℝ) 1 :=
        continuous_subtype_val.continuousAt.eventually (Ioo_mem_nhds hc hc')
      filter_upwards [hinterior] with p hp
      have heq := h.cluster_number_deriv_equation critical p.val hc hc' hfixed hp.1 hp.2
      rw [← hderivative] at heq
      change deriv rule.network.clusterNumberAnalyticExtension p.val =
        crossing.derivative.eval p.val / (rule.edges : ℝ) *
          deriv rule.network.clusterNumberAnalyticExtension (rule.network.reliability p.val) +
            (((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
              forcing.derivative.eval p.val) / (rule.edges : ℝ)
      dsimp [forcing] at *
      rw [div_mul_eq_mul_div, ← add_div]
      apply (eq_div_iff hmass.ne').mpr
      nlinarith
  have hwithin := (continuousWithinAt_iff_continuousAt_restrict
    (deriv rule.network.clusterNumberAnalyticExtension) center.property).mpr hcontinuous
  exact hwithin.continuousAt (Icc_mem_nhds hc hc')

theorem Classical.cluster_number_contDiffOn_one {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ContDiffOn ℝ 1 rule.network.clusterNumberAnalyticExtension (Ioo (0 : ℝ) 1) := by
  rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
  refine ⟨?_, by simp, ?_⟩
  · intro p hp
    exact (h.cluster_number_differentiableAt critical p hc hc' hfixed hp.1.le hp.2.le).differentiableWithinAt
  rw [contDiffOn_zero]
  intro p hp
  by_cases heq : p = critical
  · subst p
    exact (h.cluster_number_deriv_continuousAt_critical critical hc hc' hfixed).continuousWithinAt
  exact (h.cluster_number_analyticAt_offcritical critical p hc hc' hfixed hp.1.le hp.2.le heq).deriv.continuousAt.continuousWithinAt

end
end Universality.Rule


