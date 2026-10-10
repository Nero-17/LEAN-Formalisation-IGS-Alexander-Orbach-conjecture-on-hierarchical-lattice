import Universality.Analysis.LocalRenormalizationResponse
import Mathlib.Analysis.Normed.Group.Bounded

namespace Universality
noncomputable section
open Filter Set
open scoped Topology

/-- A response continuous off a repelling point is continuous at that point
when its local scalar renormalization coefficient has modulus less than one.
Compactness supplies the exit bound; orbit escape is an explicit dynamical
hypothesis, independent of the response being studied. -/
theorem continuousAt_of_compact_renormalization
    {space : Type*} [MetricSpace space] [CompactSpace space]
    (iteration : space → space) (response coefficient forcing : space → ℝ) (center : space)
    (outerRadius : ℝ) (houterRadius : 0 < outerRadius)
    (hiteration : ContinuousAt iteration center) (hfixed : iteration center = center)
    (hescape : ∀ point ≠ center, ∃ n : ℕ, outerRadius ≤ dist (iteration^[n] point) center)
    (hresponse : ContinuousOn response {center}ᶜ)
    (hcoefficient : ContinuousAt coefficient center)
    (hforcing : ContinuousAt forcing center) (hcontract : |coefficient center| < 1)
    (hequation : ∀ᶠ point in 𝓝 center,
      response point = coefficient point * response (iteration point) + forcing point) :
    ContinuousAt response center := by
  let contraction := (|coefficient center| + 1) / 2
  have hcontractionNonneg : 0 ≤ contraction := by dsimp [contraction]; positivity
  have hcontraction : contraction < 1 := by dsimp [contraction]; linarith
  have hcoefficientSmall : ∀ᶠ point in 𝓝 center, |coefficient point| ≤ contraction := by
    filter_upwards [hcoefficient.abs.eventually (gt_mem_nhds
      (show |coefficient center| < contraction by dsimp [contraction]; linarith))] with point hp
    exact hp.le
  have hforcingBound : ∀ᶠ point in 𝓝 center, |forcing point| ≤ |forcing center| + 1 := by
    filter_upwards [hforcing.abs.eventually (gt_mem_nhds (show
      |forcing center| < |forcing center| + 1 by linarith))] with point hp
    exact hp.le
  obtain ⟨neighborhood, hneighborhood, hlocal⟩ := Metric.eventually_nhds_iff.mp
    (hequation.and (hcoefficientSmall.and hforcingBound))
  let radius := min neighborhood outerRadius
  have hradius : 0 < radius := lt_min hneighborhood houterRadius
  have houtsideClosed : IsClosed {point : space | radius ≤ dist point center} :=
    isClosed_le continuous_const (continuous_id.dist continuous_const)
  have houtsideCompact : IsCompact {point : space | radius ≤ dist point center} :=
    houtsideClosed.isCompact
  have houtsideSubset : {point : space | radius ≤ dist point center} ⊆ {center}ᶜ := by
    intro point hp
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro heq
    subst point
    have hzero : radius ≤ 0 := by simpa only [Set.mem_setOf_eq, dist_self] using hp
    linarith
  obtain ⟨exitBound, hexitBound⟩ := houtsideCompact.exists_bound_of_continuousOn
    (hresponse.mono houtsideSubset)
  let bound := max (max exitBound |response center|)
    ((|forcing center| + 1) / (1 - contraction))
  have hboundCenter : |response center| ≤ bound :=
    (le_max_right exitBound _).trans (le_max_left _ _)
  have hboundNonneg : 0 ≤ bound := (abs_nonneg _).trans hboundCenter
  have hbalance : contraction * bound + (|forcing center| + 1) ≤ bound := by
    have h := (div_le_iff₀ (sub_pos.mpr hcontraction)).mp
      (le_max_right (max exitBound |response center|)
        ((|forcing center| + 1) / (1 - contraction)))
    change |forcing center| + 1 ≤ bound * (1 - contraction) at h
    nlinarith
  have houtside (point : space) (hp : radius ≤ dist point center) : |response point| ≤ bound := by
    have h := hexitBound point hp
    rw [Real.norm_eq_abs] at h
    exact h.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hrecursion (point : space) (hp : dist point center < radius) :
      |response point| ≤ contraction * |response (iteration point)| + (|forcing center| + 1) := by
    obtain ⟨heq, hcoef, hforce⟩ := hlocal (y := point) (hp.trans_le (min_le_left _ _))
    rw [heq]
    exact (abs_add_le _ _).trans (by
      rw [abs_mul]
      exact add_le_add (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) hforce)
  have hglobal (point : space) : |response point| ≤ bound := by
    by_cases heq : point = center
    · simpa [heq] using hboundCenter
    obtain ⟨depth, hdepth⟩ := hescape point heq
    apply bounded_response_from_finite_exit iteration response (fun x => dist x center)
      radius contraction (|forcing center| + 1) bound hcontractionNonneg hbalance
      (fun x hx => houtside x (by simpa only [abs_of_nonneg dist_nonneg] using hx))
      (fun x hx => hrecursion x (by simpa only [abs_of_nonneg dist_nonneg] using hx)) point depth
    simpa only [abs_of_nonneg dist_nonneg] using (min_le_right neighborhood outerRadius).trans hdepth
  have hcenterEquation := hequation.self_of_nhds
  rw [hfixed] at hcenterEquation
  have herror : Tendsto (fun point => coefficient point * response center + forcing point -
      response center) (𝓝 center) (𝓝 0) := by
    have h := ((hcoefficient.tendsto.mul_const (response center)).add hforcing.tendsto).sub_const
      (response center)
    simpa only [← hcenterEquation, sub_self] using h
  have hzero := tendsto_zero_of_local_renormalization (𝓝 center) iteration
    (fun point => response point - response center)
    (fun point => coefficient point * response center + forcing point - response center)
    contraction (bound + |response center|) hcontractionNonneg hcontraction
    (by simpa only [hfixed] using hiteration.tendsto)
    (Eventually.of_forall (fun point => (abs_sub _ _).trans (add_le_add (hglobal point) le_rfl)))
    herror (by
      filter_upwards [hequation, hcoefficientSmall] with point heq hcoef
      have hid : response point - response center = coefficient point *
          (response (iteration point) - response center) +
          (coefficient point * response center + forcing point - response center) := by
        rw [heq]
        ring
      rw [hid]
      exact (abs_add_le _ _).trans (by
        rw [abs_mul]
        exact add_le_add (mul_le_mul_of_nonneg_right hcoef (abs_nonneg _)) le_rfl))
  change Tendsto response (𝓝 center) (𝓝 (response center))
  simpa only [sub_add_cancel, zero_add] using hzero.add_const (response center)

end
end Universality

