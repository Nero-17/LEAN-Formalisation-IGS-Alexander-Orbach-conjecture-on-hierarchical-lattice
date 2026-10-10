import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality.Geometry
noncomputable section
open Set Metric Filter
open scoped Topology NNReal

variable {Alphabet Ambient : Type*} [MetricSpace Ambient]

/-- If first-level images cover the space, every point belongs to a copy at
any prescribed depth. The copy has the exact iterated distance factor. -/
theorem exists_similarity_containing (maps : Alphabet → Ambient → Ambient)
    (contraction : ℝ)
    (hdist : ∀ symbol first second, dist (maps symbol first) (maps symbol second) =
      contraction * dist first second)
    (hcover : ∀ point : Ambient, ∃ symbol preimage, maps symbol preimage = point)
    (depth : ℕ) (point : Ambient) :
    ∃ copy : Ambient → Ambient,
      (∀ first second, dist (copy first) (copy second) = contraction ^ depth * dist first second) ∧
      point ∈ Set.range copy := by
  induction depth generalizing point with
  | zero => exact ⟨id, by simp, ⟨point, rfl⟩⟩
  | succ depth ih =>
    obtain ⟨symbol, preimage, hpreimage⟩ := hcover point
    obtain ⟨copy, hcopy, witness, hwitness⟩ := ih preimage
    refine ⟨maps symbol ∘ copy, ?_, ⟨witness, ?_⟩⟩
    · intro first second
      simp only [Function.comp_apply, hdist, hcopy, pow_succ]
      ring
    · simpa only [Function.comp_apply, hwitness] using hpreimage

/-- A positive value of a Lipschitz boundary function contains an entire
small similarity copy with a uniform positive boundary margin. -/
theorem exists_internal_similarity [CompactSpace Ambient]
    (maps : Alphabet → Ambient → Ambient) (contraction : ℝ)
    (hcontraction : 0 ≤ contraction) (hcontraction_lt_one : contraction < 1)
    (hdist : ∀ symbol first second, dist (maps symbol first) (maps symbol second) =
      contraction * dist first second)
    (hcover : ∀ point : Ambient, ∃ symbol preimage, maps symbol preimage = point)
    (height : Ambient → ℝ) (hheight : LipschitzWith 1 height)
    (point : Ambient) (hpositive : 0 < height point) :
    ∃ depth : ℕ, ∃ copy : Ambient → Ambient, ∃ margin : ℝ, 0 < margin ∧
      (∀ first second, dist (copy first) (copy second) = contraction ^ depth * dist first second) ∧
      ∀ x, margin ≤ height (copy x) := by
  have htendsto : Tendsto (fun depth : ℕ => contraction ^ depth * diam (Set.univ : Set Ambient))
      atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hcontraction hcontraction_lt_one).mul_const
      (diam (Set.univ : Set Ambient))
  obtain ⟨depth, hdepth⟩ := (htendsto.eventually (gt_mem_nhds (half_pos hpositive))).exists
  obtain ⟨copy, hcopy, witness, hwitness⟩ :=
    exists_similarity_containing maps contraction hdist hcover depth point
  refine ⟨depth, copy, height point / 2, half_pos hpositive, hcopy, ?_⟩
  intro x
  have hnear : dist (copy x) point < height point / 2 := by
    conv_lhs => rw [← hwitness, hcopy]
    exact (mul_le_mul_of_nonneg_left
      (dist_le_diam_of_mem isCompact_univ.isBounded (Set.mem_univ x) (Set.mem_univ witness))
      (pow_nonneg hcontraction _)).trans_lt hdepth
  have hheightNear := hheight.dist_le_mul point (copy x)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hheightNear
  have hbound := (le_abs_self (height point - height (copy x))).trans hheightNear
  rw [dist_comm point] at hbound
  linarith

end
end Universality.Geometry