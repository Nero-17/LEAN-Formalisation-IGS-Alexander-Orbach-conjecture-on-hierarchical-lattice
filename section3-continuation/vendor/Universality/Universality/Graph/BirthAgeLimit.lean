import Universality.Graph.BirthAgeCounting
import Universality.Graph.VolumeLimit

namespace Universality.Rule
noncomputable section
open Filter
open scoped Topology

/-- The probability of a given age under the actual uniform finite vertex law.
The two terminal vertices are outside these interior-vertex fibres. -/
def finiteRootAgeProbability (rule : Rule) (depth age : ℕ) : ℝ :=
  (Fintype.card {v : (rule.generation depth).network.InteriorVertex //
    rule.interiorVertexAge depth v = age} : ℝ) / (rule.generation depth).vertices

theorem finiteRootAgeProbability_shift (rule : Rule) (depth age : ℕ)
    (hedges : 1 < rule.edges) :
    rule.finiteRootAgeProbability (depth + age) age =
      (((rule.vertices : ℝ) - 2) / (rule.edges : ℝ) ^ (age + 1)) /
        ((rule.generation (depth + age)).vertices / (rule.edges : ℝ) ^ (depth + age + 1)) := by
  have hm : (rule.edges : ℝ) ≠ 0 := by exact_mod_cast (by omega : rule.edges ≠ 0)
  have hv : ((rule.generation (depth + age)).vertices : ℝ) ≠ 0 := by
    exact_mod_cast (by have := (rule.generation (depth + age)).network.two_le_vertices; omega :
      (rule.generation (depth + age)).vertices ≠ 0)
  unfold finiteRootAgeProbability
  rw [rule.card_interiorVertexAge (depth + age) age (by omega)]
  simp only [Nat.add_sub_cancel, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_sub rule.network.two_le_vertices, Nat.cast_ofNat]
  rw [show depth + age + 1 = depth + (age + 1) by omega, pow_add]
  field_simp [hm, hv] <;> ring

/-- The geometric age law is obtained from actual vertex counts and the actual
generation-volume limit; it is not assumed as an input to the graph model. -/
theorem finiteRootAgeProbability_tendsto (rule : Rule) (hedges : 1 < rule.edges)
    (hvertices : 2 < rule.vertices) (age : ℕ) :
    Tendsto (fun depth => rule.finiteRootAgeProbability depth age) atTop
      (𝓝 (((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1))) := by
  have hm : (1 : ℝ) < rule.edges := by exact_mod_cast hedges
  have hv : (2 : ℝ) < rule.vertices := by exact_mod_cast hvertices
  have hden : ((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1) ≠ 0 :=
    ne_of_gt (div_pos (sub_pos.mpr hv) (sub_pos.mpr hm))
  apply (tendsto_add_atTop_iff_nat age).mp
  simp_rw [rule.finiteRootAgeProbability_shift _ age hedges]
  have hvolume : Tendsto (fun depth : ℕ =>
      ((rule.generation (depth + age)).vertices : ℝ) /
        (rule.edges : ℝ) ^ (depth + age + 1)) atTop
      (𝓝 (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1))) := by
    simpa only [Function.comp_def, Nat.add_comm] using
      (rule.generation_volume_ratio_tendsto hedges).comp (tendsto_add_atTop_nat age)
  have hlim := (tendsto_const_nhds (x :=
      ((rule.vertices : ℝ) - 2) / (rule.edges : ℝ) ^ (age + 1))).div
    hvolume hden
  have heq : ((rule.vertices : ℝ) - 2) / (rule.edges : ℝ) ^ (age + 1) /
      (((rule.vertices : ℝ) - 2) / ((rule.edges : ℝ) - 1)) =
        ((rule.edges : ℝ) - 1) / (rule.edges : ℝ) ^ (age + 1) := by
    field_simp [ne_of_gt (lt_trans zero_lt_one hm),
      ne_of_gt (sub_pos.mpr hv), ne_of_gt (sub_pos.mpr hm)] <;> ring
  rw [heq] at hlim
  exact hlim

end
end Universality.Rule
