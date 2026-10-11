import Universality.Percolation.GenerationMomentComparison
import Universality.Percolation.ConditionalWeightComparison
import Universality.Percolation.RepellingOrbitSum
import Universality.Percolation.VertexMomentComparison

namespace Universality.Rule
noncomputable section
open Filter FiniteNetwork
open scoped Topology

/-- Uniform comparison with the actual critical moments throughout any
finite orbit segment that stays in a sufficiently small critical interval.
The interval and distortion constant work simultaneously for all orders. -/
theorem Classical.preexit_moment_distortion {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ neighborhood rate lower : ℝ, 0 < neighborhood ∧ 0 < rate ∧ 1 < lower ∧
      ∀ radius : ℝ, 0 < radius → radius ≤ neighborhood → ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) → ∀ state order,
          (rule.generation n).network.conditionalVertexMoment p state order ≤
            Real.exp (rate * (radius / (lower - 1) + radius)) ^ order * (rule.generation n).network.conditionalVertexMoment critical state order ∧
          (rule.generation n).network.conditionalVertexMoment critical state order ≤
            Real.exp (rate * (radius / (lower - 1) + radius)) ^ order * (rule.generation n).network.conditionalVertexMoment p state order := by
  obtain ⟨rate, hrate, hweights⟩ := rule.network.conditionalCellWeight_local_exponential_comparison
    critical hc hc' (by rwa [hfixed]) (by rwa [hfixed])
  obtain ⟨lower, hlower, hexpansion⟩ := h.local_reliability_distance_expansion critical hc hc' hfixed
  obtain ⟨neighborhood, hneighborhood, hball⟩ := Metric.eventually_nhds_iff.mp (hweights.and hexpansion)
  refine ⟨neighborhood, rate, lower, hneighborhood, hrate, hlower, ?_⟩
  intro radius hradius hradiusBound p hp hp' n horbit state order
  have hlocal (point : ℝ) (hpoint : |point - critical| < radius) :=
    hball (y := point) (by simpa only [Real.dist_eq] using hpoint.trans_le hradiusBound)
  have hsum := finite_repelling_orbit_sum_bound rule.network.reliability critical radius lower p hlower n
    (fun point hpoint => (hlocal point hpoint).2) horbit
  let factor : ℕ → ℝ := fun j => Real.exp (rate * |rule.network.reliability^[j] p - critical|)
  have hfactor (j : ℕ) : 1 ≤ factor j :=
    Real.one_le_exp_iff.mpr (mul_nonneg hrate.le (abs_nonneg _))
  have hproduct : (∏ j ∈ Finset.range (n + 1), factor j) ≤
      Real.exp (rate * (radius / (lower - 1) + radius)) := by
    unfold factor
    rw [← Real.exp_sum, ← Finset.mul_sum]
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hsum hrate.le)
  have hcriticalOrbit (j : ℕ) : rule.network.reliability^[j] critical = critical := by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih, hfixed]
  have hforward := h.generation_moments_parameter_comparison critical p hc hc' hp hp' factor n
    (fun j _ => hfactor j) (by
      intro j hj opened configuration
      rw [hcriticalOrbit]
      exact ((hlocal _ (horbit j hj)).1 opened configuration).1) n le_rfl state order
  have hbackward := h.generation_moments_parameter_comparison p critical hp hp' hc hc' factor n
    (fun j _ => hfactor j) (by
      intro j hj opened configuration
      rw [hcriticalOrbit]
      exact ((hlocal _ (horbit j hj)).1 opened configuration).2) n le_rfl state order
  have hproductNonneg : 0 ≤ ∏ j ∈ Finset.range (n + 1), factor j :=
    Finset.prod_nonneg (fun j _ => (Real.exp_pos _).le)
  have hpower := pow_le_pow_left₀ hproductNonneg hproduct order
  exact ⟨hforward.trans (mul_le_mul_of_nonneg_right hpower
      ((rule.generation n).network.conditionalInternalMoment_nonneg critical hc.le hc'.le _ _ _ _)),
    hbackward.trans (mul_le_mul_of_nonneg_right hpower
      ((rule.generation n).network.conditionalInternalMoment_nonneg p hp.le hp'.le _ _ _ _))⟩

/-- The comparison constant can be chosen arbitrarily close to one by
shrinking the critical neighborhood, uniformly over the orbit length. -/
theorem Classical.preexit_moment_comparison_with_distortion {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (distortion : ℝ) (hdistortion : 1 < distortion) :
    ∃ radius : ℝ, 0 < radius ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) → ∀ state order,
          (rule.generation n).network.conditionalVertexMoment p state order ≤
            distortion ^ order * (rule.generation n).network.conditionalVertexMoment critical state order ∧
          (rule.generation n).network.conditionalVertexMoment critical state order ≤
            distortion ^ order * (rule.generation n).network.conditionalVertexMoment p state order := by
  obtain ⟨neighborhood, rate, lower, hneighborhood, hrate, hlower, hb⟩ := h.preexit_moment_distortion critical hc hc' hfixed
  have hcoefficient : 0 < rate * (1 / (lower - 1) + 1) := by positivity
  have hlog : 0 < Real.log distortion := Real.log_pos hdistortion
  let radius := min neighborhood (Real.log distortion / (rate * (1 / (lower - 1) + 1)))
  have hradius : 0 < radius := lt_min hneighborhood (div_pos hlog hcoefficient)
  have hsmall : rate * (radius / (lower - 1) + radius) ≤ Real.log distortion := by
    have hh : radius ≤ Real.log distortion / (rate * (1 / (lower - 1) + 1)) := min_le_right _ _
    have hm := (le_div_iff₀ hcoefficient).mp hh
    calc
      _ = radius * (rate * (1 / (lower - 1) + 1)) := by ring
      _ ≤ _ := hm
  have hexp : Real.exp (rate * (radius / (lower - 1) + radius)) ≤ distortion := by
    simpa only [Real.exp_log (zero_lt_one.trans hdistortion)] using Real.exp_le_exp.mpr hsmall
  refine ⟨radius, hradius, ?_⟩
  intro p hp hp' n horbit state order
  have hh := hb radius hradius (min_le_left _ _) p hp hp' n horbit state order
  have hpower := pow_le_pow_left₀ (Real.exp_pos _).le hexp order
  exact ⟨hh.1.trans (mul_le_mul_of_nonneg_right hpower
      ((rule.generation n).network.conditionalInternalMoment_nonneg critical hc.le hc'.le _ _ _ _)),
    hh.2.trans (mul_le_mul_of_nonneg_right hpower
      ((rule.generation n).network.conditionalInternalMoment_nonneg p hp.le hp'.le _ _ _ _))⟩

/-- Uniform pre-exit spectral-scale two-sided bounds for every natural
moment order, for the actual conditional internal vertex mass. -/
theorem Classical.preexit_moment_bounds {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ radius : ℝ, 0 < radius ∧ ∀ order : ℕ, ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧
      ∀ p, 0 < p → p < 1 → ∀ n : ℕ,
        (∀ j ≤ n, |rule.network.reliability^[j] p - critical| < radius) → ∀ state,
          lower * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * n) ≤
            (rule.generation n).network.conditionalVertexMoment p state order ∧
          (rule.generation n).network.conditionalVertexMoment p state order ≤
            upper * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * n) := by
  let distortion : ℝ := 2
  have hdistortion : 0 < distortion := by norm_num [distortion]
  obtain ⟨radius, hradius, hcomparison⟩ := h.preexit_moment_comparison_with_distortion critical hc hc' hfixed distortion (by norm_num [distortion])
  refine ⟨radius, hradius, ?_⟩
  intro order
  obtain ⟨lower, upper, hlower, hupper, hcritical⟩ := h.internal_vertex_moment_comparison critical hc hc' hfixed order
  refine ⟨lower / distortion ^ order, distortion ^ order * upper,
    div_pos hlower (pow_pos hdistortion _), mul_pos (pow_pos hdistortion _) hupper, ?_⟩
  intro p hp hp' n horbit state
  have hb := hcomparison p hp hp' n horbit state order
  constructor
  · have hh := (hcritical n state).1.trans hb.2
    calc
      _ = (lower * ((spectralRadius ℂ ((rule.network.massMatrix critical).map Complex.ofReal)).toReal) ^ (order * n)) /
          distortion ^ order := by ring
      _ ≤ _ := (div_le_iff₀ (pow_pos hdistortion order)).mpr
        (by simpa only [mul_comm ((rule.generation n).network.conditionalVertexMoment p state order)] using hh)
  · exact hb.1.trans (by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hcritical n state).2
        (pow_nonneg hdistortion.le _))

end
end Universality.Rule

