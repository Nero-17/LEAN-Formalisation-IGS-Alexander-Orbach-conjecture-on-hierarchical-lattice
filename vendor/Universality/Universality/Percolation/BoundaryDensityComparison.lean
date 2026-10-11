import Universality.Percolation.RootedLimitBoundaryMass

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology
set_option maxHeartbeats 0

theorem generation_boundary_mass_edge_density_limit (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1) :
    Tendsto (fun n : ℕ => (rule.generation n).network.expectedInternalBoundaryMass p /
      (rule.edges : ℝ) ^ (n + 1)) atTop
      (𝓝 ((((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) * rule.escapingRootMass p)) := by
  have hm := (rule.generation_volume_ratio_tendsto hedges).mul
    (rule.generation_boundary_mass_density_limit hedges hvertices hp hp')
  convert hm using 1
  ext n
  have hv : ((rule.generation n).vertices : ℝ) ≠ 0 := by
    have h := (rule.generation n).network.two_le_vertices
    exact_mod_cast (show (rule.generation n).vertices ≠ 0 by omega)
  have he : (rule.edges : ℝ) ≠ 0 := by exact_mod_cast (show rule.edges ≠ 0 by omega)
  field_simp [hv, he]
  <;> ring

theorem escapingRootMass_le_of_shifted_boundary_bound (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p q scale : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (offset : ℕ)
    (hbound : ∀ n, (rule.generation (offset + n)).network.expectedInternalBoundaryMass p ≤
      scale * (rule.generation n).network.expectedInternalBoundaryMass q) :
    rule.escapingRootMass p ≤ scale / (rule.edges : ℝ) ^ offset * rule.escapingRootMass q := by
  have hm : 0 < (rule.edges : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hedges)
  have hcoefficient : 0 < ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1) := by
    have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
    have he : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
    exact div_pos (sub_pos.mpr hv) (sub_pos.mpr he)
  have hshift : Tendsto (fun n : ℕ => offset + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat offset
  have hfirst := (rule.generation_boundary_mass_edge_density_limit hedges hvertices hp hp').comp hshift
  have hsecond := (rule.generation_boundary_mass_edge_density_limit hedges hvertices hq hq').const_mul
    (scale / (rule.edges : ℝ) ^ offset)
  have hlimit := le_of_tendsto_of_tendsto hfirst hsecond (Eventually.of_forall (fun n => show
      (rule.generation (offset + n)).network.expectedInternalBoundaryMass p / (rule.edges : ℝ) ^ (offset + n + 1) ≤
        scale / (rule.edges : ℝ) ^ offset * ((rule.generation n).network.expectedInternalBoundaryMass q /
          (rule.edges : ℝ) ^ (n + 1)) from by
    calc
      _ ≤ scale * (rule.generation n).network.expectedInternalBoundaryMass q / (rule.edges : ℝ) ^ (offset + n + 1) :=
        div_le_div_of_nonneg_right (hbound n) (pow_nonneg hm.le _)
      _ = _ := by
        rw [show offset + n + 1 = offset + (n + 1) by omega, pow_add]
        field_simp [hm.ne']
        <;> ring))
  apply le_of_mul_le_mul_left (a := ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) ?_ hcoefficient
  simpa only [mul_left_comm] using hlimit

theorem escapingRootMass_ge_of_shifted_boundary_bound (rule : Rule)
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p q scale : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1) (hq : 0 ≤ q) (hq' : q ≤ 1)
    (offset : ℕ)
    (hbound : ∀ n, scale * (rule.generation n).network.expectedInternalBoundaryMass q ≤
      (rule.generation (offset + n)).network.expectedInternalBoundaryMass p) :
    scale / (rule.edges : ℝ) ^ offset * rule.escapingRootMass q ≤ rule.escapingRootMass p := by
  have hm : 0 < (rule.edges : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hedges)
  have hcoefficient : 0 < ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1) := by
    have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
    have he : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
    exact div_pos (sub_pos.mpr hv) (sub_pos.mpr he)
  have hshift : Tendsto (fun n : ℕ => offset + n) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat offset
  have hfirst := (rule.generation_boundary_mass_edge_density_limit hedges hvertices hq hq').const_mul
    (scale / (rule.edges : ℝ) ^ offset)
  have hsecond := (rule.generation_boundary_mass_edge_density_limit hedges hvertices hp hp').comp hshift
  have hlimit := le_of_tendsto_of_tendsto hfirst hsecond (Eventually.of_forall (fun n => show
      scale / (rule.edges : ℝ) ^ offset * ((rule.generation n).network.expectedInternalBoundaryMass q /
          (rule.edges : ℝ) ^ (n + 1)) ≤
        (rule.generation (offset + n)).network.expectedInternalBoundaryMass p / (rule.edges : ℝ) ^ (offset + n + 1) from by
    calc
      _ = scale * (rule.generation n).network.expectedInternalBoundaryMass q / (rule.edges : ℝ) ^ (offset + n + 1) := by
        rw [show offset + n + 1 = offset + (n + 1) by omega, pow_add]
        field_simp [hm.ne']
        <;> ring
      _ ≤ _ := div_le_div_of_nonneg_right (hbound n) (pow_nonneg hm.le _)))
  apply le_of_mul_le_mul_left (a := ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) ?_ hcoefficient
  simpa only [mul_left_comm] using hlimit

end
end Universality.Rule
