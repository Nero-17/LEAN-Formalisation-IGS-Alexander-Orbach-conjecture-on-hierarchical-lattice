import Universality.Analysis.CompactRenormalizationResponse
import Universality.Analysis.CompactAffineResponse

namespace Universality
noncomputable section
open Set Filter
open scoped Topology

theorem lower_response_from_finite_exit {space : Type*}
    (iteration : space → space) (response distance : space → ℝ) (radius bound : ℝ)
    (hexit : ∀ point, radius ≤ distance point → bound ≤ response point)
    (hlocal : ∀ point, distance point < radius → response (iteration point) ≤ response point)
    (point : space) (depth : ℕ) (hdepth : radius ≤ distance (iteration^[depth] point)) :
    bound ≤ response point := by
  induction depth generalizing point with
  | zero => exact hexit point hdepth
  | succ depth ih =>
      by_cases houtside : radius ≤ distance point
      · exact hexit point houtside
      · apply (ih (iteration point) ?_).trans (hlocal point (lt_of_not_ge houtside))
        simpa only [Function.iterate_succ_apply] using hdepth

/-- An increasing backward response is uniformly positive away from its repelling
center. Positivity and continuity are required only away from that center. -/
theorem positive_lower_bound_of_compact_escape
    {space : Type*} [MetricSpace space] [CompactSpace space]
    (iteration : space → space) (response : space → ℝ) (center : space)
    (outerRadius : ℝ) (houterRadius : 0 < outerRadius)
    (hescape : ∀ point ≠ center, ∃ n : ℕ, outerRadius ≤ dist (iteration^[n] point) center)
    (hresponse : ContinuousOn response {center}ᶜ)
    (hpositive : ∀ point ≠ center, 0 < response point)
    (hlocal : ∀ᶠ point in 𝓝 center, response (iteration point) ≤ response point) :
    ∃ bound > 0, ∀ point ≠ center, bound ≤ response point := by
  obtain ⟨neighborhood, hneighborhood, hrecursion⟩ := Metric.eventually_nhds_iff.mp hlocal
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
  have hexitBound : ∃ bound > 0, ∀ point, radius ≤ dist point center → bound ≤ response point := by
    by_cases hnonempty : {point : space | radius ≤ dist point center}.Nonempty
    · obtain ⟨minimum, hminimumMem, hminimum⟩ := houtsideCompact.exists_isMinOn
        hnonempty (hresponse.mono houtsideSubset)
      refine ⟨response minimum, hpositive minimum ?_, fun point hp => hminimum hp⟩
      simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using houtsideSubset hminimumMem
    · refine ⟨1, by norm_num, ?_⟩
      intro point hp
      exact (hnonempty ⟨point, hp⟩).elim
  obtain ⟨bound, hbound, hexitBound⟩ := hexitBound
  refine ⟨bound, hbound, ?_⟩
  intro point hpoint
  obtain ⟨depth, hdepth⟩ := hescape point hpoint
  apply lower_response_from_finite_exit iteration response (fun point => dist point center)
    radius bound hexitBound (fun point hp => hrecursion (hp.trans_le (min_le_left _ _))) point depth
  exact (min_le_right neighborhood outerRadius).trans hdepth

end
end Universality
