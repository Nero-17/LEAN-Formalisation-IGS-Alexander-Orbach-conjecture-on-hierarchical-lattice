import Universality.Analysis.QuadraticRenormalization
import Universality.Percolation.ClusterNumberContinuity
import Universality.Percolation.ClassicalClusterNumber
import Universality.Percolation.ClusterNumberNormalization
import Universality.Percolation.RenormalisationLimits

namespace Universality.Rule
noncomputable section
open FiniteNetwork Polynomial Filter
open scoped Topology
set_option maxHeartbeats 600000

/-- The actual bounded density has a quadratic remainder after its uniquely
determined affine Taylor term at the critical point. This proves first-order
regularity without any analyticity or differentiability hypothesis on the density. -/
theorem Classical.cluster_number_linear_remainder {rule : Rule} (h : rule.Classical)
    (critical : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) :
    ∃ coefficient bound : ℝ, 0 ≤ bound ∧
      ((rule.edges : ℝ) - deriv rule.network.reliability critical) * coefficient =
        ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2) *
          (rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)).derivative.eval critical ∧
      ∀ p : Set.Icc (0 : ℝ) 1,
        |rule.network.clusterNumberSeries p -
            rule.network.clusterNumberSeries ⟨critical, hc.le, hc'.le⟩ -
            coefficient * (p.val - critical)| ≤ bound * (p.val - critical) ^ 2 := by
  let crossing : Polynomial ℝ := rule.network.reliabilityPolynomial.map (Rat.castHom ℝ)
  let forcing : Polynomial ℝ := rule.network.internalClusterPolynomial.map (Int.castRingHom ℝ)
  let normalization : ℝ := ((rule.edges : ℝ) - 1) / ((rule.vertices : ℝ) - 2)
  let center : Set.Icc (0 : ℝ) 1 := ⟨critical, hc.le, hc'.le⟩
  have hcrossing (p : ℝ) : crossing.eval p = rule.network.reliability p := by
    simp only [crossing, Polynomial.eval_map, reliabilityPolynomial_eval]
  have hforcing (p : ℝ) : forcing.eval p = rule.network.expectedInternalClusterNumber p := by
    simp only [forcing, Polynomial.eval_map, internalClusterPolynomial_eval]
  have hderivative : crossing.derivative.eval critical = deriv rule.network.reliability critical := by
    dsimp [crossing]
    rw [Polynomial.derivative_map, Polynomial.eval_map,
      (rule.network.hasDerivAt_reliability critical).deriv]
  have hrepelling : 1 < crossing.derivative.eval critical := by
    rw [hderivative]
    exact rule.network.interior_fixed_point_strictly_unstable critical hc hc' hfixed h.scale
  have hsquare : crossing.derivative.eval critical ^ 2 < (rule.edges : ℝ) := by
    rw [hderivative]
    exact rule.network.pivotal_response_sq_lt_edges critical hc hc' hfixed h.scale
  have hmass : (0 : ℝ) < rule.edges := by nlinarith
  have hgap : 0 < (rule.edges : ℝ) - crossing.derivative.eval critical := by nlinarith
  let coefficient := normalization * forcing.derivative.eval critical /
    ((rule.edges : ℝ) - crossing.derivative.eval critical)
  have hcoefficient : ((rule.edges : ℝ) - crossing.derivative.eval critical) * coefficient =
      normalization * forcing.derivative.eval critical := by
    dsimp [coefficient]
    field_simp [hgap.ne']
  let remainder (p : Set.Icc (0 : ℝ) 1) := rule.network.clusterNumberSeries p -
    rule.network.clusterNumberSeries center - coefficient * (p.val - critical)
  obtain ⟨crossingBound, hcrossingBound, hcrossingRemainder⟩ :=
    polynomial_quadratic_remainder_bound crossing critical
  obtain ⟨forcingBound, hforcingBound, hforcingRemainder⟩ :=
    polynomial_quadratic_remainder_bound forcing critical
  let defectBound := |normalization| * forcingBound + |coefficient| * crossingBound
  have hdefectBound : 0 ≤ defectBound := by dsimp [defectBound]; positivity
  have hdefect (p : Set.Icc (0 : ℝ) 1) :
      |(rule.edges : ℝ) * remainder p - remainder (rule.network.unitReliability p)| ≤
        defectBound * (p.val - critical) ^ 2 := by
    have hpEq := rule.network.clusterNumberSeries_equation h.edges_gt_one p
    have hcEq := rule.network.clusterNumberSeries_equation h.edges_gt_one center
    have hunit : rule.network.unitReliability center = center := Subtype.ext hfixed
    rw [hunit] at hcEq
    have hid : (rule.edges : ℝ) * remainder p - remainder (rule.network.unitReliability p) =
        normalization * (forcing.eval p.val - forcing.eval critical -
          forcing.derivative.eval critical * (p.val - critical)) +
        coefficient * (crossing.eval p.val - crossing.eval critical -
          crossing.derivative.eval critical * (p.val - critical)) := by
      dsimp [remainder, unitReliability]
      rw [hforcing, hforcing, hcrossing, hcrossing, hfixed]
      dsimp [center] at hcEq
      change (rule.edges : ℝ) * rule.network.clusterNumberSeries p -
        rule.network.clusterNumberSeries (rule.network.unitReliability p) =
          normalization * rule.network.expectedInternalClusterNumber p.val at hpEq
      change (rule.edges : ℝ) * rule.network.clusterNumberSeries center -
        rule.network.clusterNumberSeries center =
          normalization * rule.network.expectedInternalClusterNumber critical at hcEq
      dsimp only [unitReliability] at hpEq
      linear_combination hpEq - hcEq - (p.val - critical) * hcoefficient
    rw [hid]
    calc
      _ ≤ |normalization * (forcing.eval p.val - forcing.eval critical -
          forcing.derivative.eval critical * (p.val - critical))| +
        |coefficient * (crossing.eval p.val - crossing.eval critical -
          crossing.derivative.eval critical * (p.val - critical))| := abs_add_le _ _
      _ ≤ |normalization| * (forcingBound * (p.val - critical) ^ 2) +
          |coefficient| * (crossingBound * (p.val - critical) ^ 2) := by
        simp only [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_left (hforcingRemainder _ p.property) (abs_nonneg _))
          (mul_le_mul_of_nonneg_left (hcrossingRemainder _ p.property) (abs_nonneg _))
      _ = _ := by dsimp [defectBound]; ring
  obtain ⟨densityBound, hdensityBound⟩ := rule.network.clusterNumberSeries_bounded h.edges_gt_one
  let globalBound := 2 * densityBound + |coefficient|
  have hdensityBoundNonneg : 0 ≤ densityBound := (abs_nonneg _).trans (hdensityBound center)
  have hglobalNonneg : 0 ≤ globalBound := by dsimp [globalBound]; positivity
  have hglobal (p : Set.Icc (0 : ℝ) 1) : |remainder p| ≤ globalBound := by
    have hdev : |p.val - critical| ≤ 1 := by
      rw [abs_le]; constructor <;> linarith [p.property.1, p.property.2]
    have hlinear := mul_le_mul_of_nonneg_left hdev (abs_nonneg coefficient)
    rw [← abs_mul, mul_one] at hlinear
    have htriangle := (abs_sub (rule.network.clusterNumberSeries p -
      rule.network.clusterNumberSeries center) (coefficient * (p.val - critical))).trans
      (add_le_add (abs_sub (rule.network.clusterNumberSeries p)
        (rule.network.clusterNumberSeries center)) le_rfl)
    dsimp [remainder, globalBound]
    linarith [hdensityBound p, hdensityBound center]
  have hsqrt : crossing.derivative.eval critical < Real.sqrt (rule.edges : ℝ) := by
    nlinarith [Real.sq_sqrt hmass.le, Real.sqrt_nonneg (rule.edges : ℝ)]
  obtain ⟨expansion, hexpansionLower, hexpansionUpper⟩ := exists_between hsqrt
  have hexpansion : 0 < expansion := by linarith
  have hexpansionSquare : expansion ^ 2 < (rule.edges : ℝ) := by
    nlinarith [Real.sq_sqrt hmass.le, Real.sqrt_nonneg (rule.edges : ℝ)]
  obtain ⟨secant, hsecant, hsecantCenter⟩ := polynomial_secant_factor crossing critical
  have hsecantAbs : |secant.eval critical| < expansion := by
    rw [hsecantCenter, abs_of_pos (by linarith : 0 < crossing.derivative.eval critical)]
    exact hexpansionLower
  have hlocal := secant.continuous.continuousAt.abs.eventually (gt_mem_nhds hsecantAbs)
  obtain ⟨neighborhood, hneighborhood, hneighborhoodBound⟩ := Metric.eventually_nhds_iff.mp hlocal
  obtain ⟨radius, hradius, hradiusUpper⟩ :=
    exists_between (lt_min hneighborhood (lt_min hc (sub_pos.mpr hc')))
  have hradiusNeighborhood : radius < neighborhood := hradiusUpper.trans_le (min_le_left _ _)
  have hradiusCritical : radius < critical :=
    hradiusUpper.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hradiusOne : radius < 1 - critical :=
    hradiusUpper.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hstep (p : Set.Icc (0 : ℝ) 1) (hp : |p.val - critical| < radius) :
      |(rule.network.unitReliability p).val - critical| ≤ expansion * |p.val - critical| := by
    have hsec := hneighborhoodBound (y := p.val)
      (by simpa only [Real.dist_eq] using hp.trans hradiusNeighborhood)
    have hid := hsecant p.val
    rw [hcrossing, hcrossing, hfixed] at hid
    change |rule.network.reliability p.val - critical| ≤ _
    rw [hid, abs_mul]
    exact (mul_le_mul_of_nonneg_left hsec.le (abs_nonneg _)).trans_eq (mul_comm _ _)
  let bound := max (globalBound / radius ^ 2)
    (defectBound / ((rule.edges : ℝ) - expansion ^ 2))
  have hbound : 0 ≤ bound := le_trans (by positivity : 0 ≤ globalBound / radius ^ 2) (le_max_left _ _)
  have hbalance : defectBound + bound * expansion ^ 2 ≤ (rule.edges : ℝ) * bound := by
    have h := (div_le_iff₀ (sub_pos.mpr hexpansionSquare)).mp (le_max_right
      (globalBound / radius ^ 2) (defectBound / ((rule.edges : ℝ) - expansion ^ 2)))
    change defectBound ≤ bound * ((rule.edges : ℝ) - expansion ^ 2) at h
    nlinarith
  have houtside (p : Set.Icc (0 : ℝ) 1) (hp : radius ≤ |p.val - critical|) :
      |remainder p| ≤ bound * (p.val - critical) ^ 2 := by
    have hbase := (div_le_iff₀ (sq_pos_of_pos hradius)).mp (le_max_left
      (globalBound / radius ^ 2) (defectBound / ((rule.edges : ℝ) - expansion ^ 2)))
    have hsquared : radius ^ 2 ≤ (p.val - critical) ^ 2 := by
      simpa only [sq_abs] using pow_le_pow_left₀ hradius.le hp 2
    exact (hglobal p).trans (hbase.trans (mul_le_mul_of_nonneg_left hsquared hbound))
  refine ⟨coefficient, bound, hbound, ?_, ?_⟩
  · simpa only [hderivative] using hcoefficient
  intro p
  change |remainder p| ≤ bound * (p.val - critical) ^ 2
  by_cases heq : p.val = critical
  · have hpcenter : p = center := Subtype.ext heq
    simp [remainder, hpcenter, center]
  have hexit : ∃ n : ℕ, radius ≤ |(rule.network.unitReliability^[n] p).val - critical| := by
    rcases lt_or_gt_of_ne heq with hp | hp
    · have hlimit := (rule.network.iterate_reliability_tendsto_zero critical p.val hc hc' hfixed
        p.property.1 hp h.scale).sub_const critical |>.abs
      have hrad : radius < |(0 : ℝ) - critical| := by simpa [abs_of_pos hc] using hradiusCritical
      obtain ⟨n, hn⟩ := (hlimit.eventually (lt_mem_nhds hrad)).exists
      exact ⟨n, by simpa only [rule.network.unitReliability_iterate_val] using hn.le⟩
    · have hlimit := (rule.network.iterate_reliability_tendsto_one critical p.val hc hc' hfixed
        hp p.property.2 h.scale).sub_const critical |>.abs
      have hrad : radius < |(1 : ℝ) - critical| := by
        rwa [abs_of_pos (sub_pos.mpr hc')]
      obtain ⟨n, hn⟩ := (hlimit.eventually (lt_mem_nhds hrad)).exists
      exact ⟨n, by simpa only [rule.network.unitReliability_iterate_val] using hn.le⟩
  obtain ⟨depth, hdepth⟩ := hexit
  exact quadratic_bound_from_finite_exit rule.network.unitReliability remainder
    (fun p => p.val - critical) (rule.edges : ℝ) expansion defectBound bound radius
    hmass hexpansion.le hbound hbalance houtside hstep (fun p _ => hdefect p) p depth hdepth

end
end Universality.Rule
