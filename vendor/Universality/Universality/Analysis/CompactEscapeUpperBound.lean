import Universality.Analysis.CompactEscapeLowerBound

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology

theorem nonnegative_upper_bound_of_compact_escape
    {space : Type*} [MetricSpace space] [CompactSpace space]
    (iteration : space → space) (response : space → ℝ) (center : space)
    (outerRadius : ℝ) (houterRadius : 0 < outerRadius)
    (hescape : ∀ point ≠ center, ∃ n : ℕ, outerRadius ≤ dist (iteration^[n] point) center)
    (hresponse : ContinuousOn response {center}ᶜ)
    (hnonnegative : ∀ point, 0 ≤ response point)
    (hlocal : ∀ᶠ point in 𝓝 center, response point ≤ response (iteration point)) :
    ∃ bound > 0, ∀ point ≠ center, response point ≤ bound := by
  obtain ⟨bound, hbound, hbounds⟩ := positive_lower_bound_of_compact_escape iteration
    (fun point => 1 / (1 + response point)) center outerRadius houterRadius hescape
    (continuousOn_const.div (continuousOn_const.add hresponse)
      (fun point _ => by have := hnonnegative point; positivity))
    (fun point _ => by have := hnonnegative point; positivity) (by
      filter_upwards [hlocal] with point hp
      apply one_div_le_one_div_of_le
      · have := hnonnegative point
        positivity
      · linarith)
  refine ⟨1 / bound, one_div_pos.mpr hbound, ?_⟩
  intro point hp
  have hdenominator : 0 < 1 + response point := by have := hnonnegative point; positivity
  have hh := (le_div_iff₀ hdenominator).mp (hbounds point hp)
  apply (le_div_iff₀ hbound).mpr
  nlinarith

end
end Universality
