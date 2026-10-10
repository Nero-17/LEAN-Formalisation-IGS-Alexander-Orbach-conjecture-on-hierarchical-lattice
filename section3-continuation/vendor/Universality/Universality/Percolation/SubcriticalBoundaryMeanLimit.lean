import Universality.Percolation.SubcriticalSourceMeanLimit
import Universality.Percolation.VertexMassPlane

namespace Universality.FiniteNetwork
noncomputable section
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem conditionalVertexMass_le_vertices {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) (state : LiveState) :
    R.conditionalVertexMass p state ≤ vertices := by
  unfold conditionalVertexMass conditionalInternalMean
  calc
    _ ≤ ∑ configuration, R.conditionalCellWeight p (state == .connected) configuration * (vertices : ℝ) := by
      apply Finset.sum_le_sum
      intro configuration _
      apply mul_le_mul_of_nonneg_left _ (R.conditionalCellWeight_nonneg hp hp' _ _)
      exact_mod_cast ((R.internalSelectedMass_le true (state == LiveState.both) configuration).trans
        (by rw [R.card_interior_vertices]; exact Nat.sub_le _ _))
    _ = _ := by rw [← Finset.sum_mul, R.sum_conditionalCellWeight p hpositive hless, one_mul]

theorem expectedInternalBoundaryMass_eq_twice_source_sub_connected
    (symmetry : R.NetworkSymmetry) (hs : symmetry.vertex R.source = R.target)
    (ht : symmetry.vertex R.target = R.source) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1) :
    R.expectedInternalBoundaryMass p = 2 * R.expectedInternalSourceMass p -
      R.reliability p * R.conditionalVertexMass p .connected := by
  rw [R.expectedInternalBoundaryMass_disintegrate p hpositive hless,
    R.expectedInternalSourceMass_disintegrate p hpositive hless,
    R.conditionalVertexMass_both p symmetry hs ht]
  ring

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

theorem Classical.subcritical_connected_overlap_normalized_zero {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    Tendsto (fun n : ℕ => (rule.generation n).network.reliability p *
      (rule.generation n).network.conditionalVertexMass p .connected /
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n) atTop (𝓝 0) := by
  have hp' := hpc.trans hc'
  have hd : (1 : ℝ) ≤ rule.network.fullGraph.degree rule.network.source := by
    rw [← rule.network.sourceIncidentEdges_card_eq_degree h.simple]
    have := rule.network.sourceIncidentEdges_card_ge_two (h.connected _) h.cut
    exact_mod_cast (by omega : 1 ≤ rule.network.sourceIncidentEdges.card)
  have hm : (1 : ℝ) ≤ rule.edges := by exact_mod_cast h.edges_gt_one.le
  apply squeeze_zero (g := fun n : ℕ => ((rule.generation (n + 1)).vertices : ℝ) *
    ((rule.edges : ℝ) * (rule.generation n).network.reliability p))
  · intro n
    exact div_nonneg (mul_nonneg ((rule.generation n).network.reliability_nonneg hp.le hp'.le)
      ((rule.generation n).network.conditionalInternalMean_nonneg p hp.le hp'.le _ _ _))
      (pow_nonneg (Nat.cast_nonneg _) _)
  · intro n
    have hqnonneg := (rule.generation n).network.reliability_nonneg hp.le hp'.le
    have hqpos := ((rule.generation n).network.reliability_pos_iff_connected hp hp').mpr
      ((h.generation n).connected _)
    have hqless := (rule.generation n).network.reliability_lt_one hp hp'
    have hmassNonneg := (rule.generation n).network.conditionalInternalMean_nonneg p hp.le hp'.le true true false
    have hvolumeNat : (rule.generation n).vertices ≤ (rule.generation (n + 1)).vertices := by
      change (rule.generation n).vertices ≤ (rule.generation n * rule).vertices
      rw [mul_vertices]
      exact Nat.le_add_right _ _
    have hvolumeCast : ((rule.generation n).vertices : ℝ) ≤ ((rule.generation (n + 1)).vertices : ℝ) := by
      exact_mod_cast hvolumeNat
    have hvolume : ((rule.generation n).vertices : ℝ) ≤ ((rule.generation (n + 1)).vertices : ℝ) * rule.edges :=
      hvolumeCast.trans (le_mul_of_one_le_right (Nat.cast_nonneg _) hm)
    calc
      _ ≤ (rule.generation n).network.reliability p *
          (rule.generation n).network.conditionalVertexMass p .connected :=
        div_le_self (mul_nonneg hqnonneg hmassNonneg) (one_le_pow₀ hd)
      _ ≤ (rule.generation n).network.reliability p * ((rule.generation n).vertices : ℝ) :=
        mul_le_mul_of_nonneg_left
          ((rule.generation n).network.conditionalVertexMass_le_vertices hp.le hp'.le hqpos hqless _) hqnonneg
      _ ≤ _ := by
        have hb := mul_le_mul_of_nonneg_left hvolume hqnonneg
        nlinarith [hb]
  · exact (h.subcritical_boundary_error_summable critical p hc hc' hfixed hp.le hpc).tendsto_atTop_zero

theorem Classical.subcritical_boundary_mean_limit {rule : Rule} (h : rule.Classical)
    (critical p : ℝ) (hc : 0 < critical) (hc' : critical < 1)
    (hfixed : rule.network.reliability critical = critical) (hp : 0 < p) (hpc : p < critical) :
    ∃ limit : ℝ, 0 < limit ∧ Tendsto (fun n : ℕ =>
      (rule.generation n).network.expectedInternalBoundaryMass p /
        (rule.network.fullGraph.degree rule.network.source : ℝ) ^ n) atTop (𝓝 limit) := by
  obtain ⟨limit, hpositive, hlimit⟩ := h.subcritical_source_mean_limit critical p hc hc' hfixed hp hpc
  refine ⟨2 * limit, mul_pos (by norm_num) hpositive, ?_⟩
  have hresult := (hlimit.const_mul 2).sub
    (h.subcritical_connected_overlap_normalized_zero critical p hc hc' hfixed hp hpc)
  simp only [sub_zero] at hresult
  convert hresult using 1
  ext n
  obtain ⟨symmetry, hs, ht⟩ := (h.generation n).massAdmissible.symmetric
  rw [(rule.generation n).network.expectedInternalBoundaryMass_eq_twice_source_sub_connected
    symmetry hs ht p (((rule.generation n).network.reliability_pos_iff_connected hp (hpc.trans hc')).mpr
      ((h.generation n).connected _)) ((rule.generation n).network.reliability_lt_one hp (hpc.trans hc'))]
  ring

end
end Universality.Rule

