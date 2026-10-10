import Universality.Analysis.StoppedGeometricLogBound
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecificLimits.Basic

namespace Universality
noncomputable section
set_option maxHeartbeats 800000
open Filter

theorem spatial_geometric_log_error (response size length ratio lower upper : ℝ)
    (depth : ℕ) (hsize : 0 < size) (hlength : 1 < length) (hratio : 0 < ratio)
    (hlower : 0 < lower) (hupper : 0 < upper)
    (hsizeLower : length ^ depth ≤ size) (hsizeUpper : size ≤ length ^ (depth + 1))
    (hresponseLower : lower * ratio ^ depth ≤ response)
    (hresponseUpper : response ≤ upper * ratio ^ depth) :
    |Real.log response - (Real.log ratio / Real.log length) * Real.log size| ≤
      |Real.log lower| + |Real.log upper| + |Real.log ratio / Real.log length| * Real.log length := by
  have hlog : 0 < Real.log length := Real.log_pos hlength
  have hmass := log_error_of_geometric_comparison response ratio lower upper depth hratio hlower hupper hresponseLower hresponseUpper
  have hleft := Real.log_le_log (pow_pos (zero_lt_one.trans hlength) depth) hsizeLower
  have hright := Real.log_le_log hsize hsizeUpper
  rw [Real.log_pow] at hleft hright
  simp only [Nat.cast_add, Nat.cast_one] at hright
  have hscaleError : |(depth : ℝ) * Real.log length - Real.log size| ≤ Real.log length :=
    abs_le.mpr ⟨by nlinarith only [hright], by linarith⟩
  have heq : Real.log response - (Real.log ratio / Real.log length) * Real.log size =
      (Real.log response - (depth : ℝ) * Real.log ratio) +
        (Real.log ratio / Real.log length) * ((depth : ℝ) * Real.log length - Real.log size) := by
    field_simp [hlog.ne']
    <;> ring
  rw [heq]
  calc
    _ ≤ |Real.log response - (depth : ℝ) * Real.log ratio| +
        |(Real.log ratio / Real.log length) * ((depth : ℝ) * Real.log length - Real.log size)| := abs_add_le _ _
    _ ≤ _ := by
      rw [abs_mul]
      exact add_le_add hmass (mul_le_mul_of_nonneg_left hscaleError (abs_nonneg _))

theorem antitone_geometric_log_error (response : ℕ → ℝ) (hanti : Antitone response)
    (length bound : ℕ) (hlength : 1 < length)
    (ratio lower upper : ℝ) (hratio : 0 < ratio) (hlower : 0 < lower) (hupper : 0 < upper)
    (hlowerBound : ∀ n, lower * ratio ^ n ≤ response (length ^ n))
    (hupperBound : ∀ n, response (bound * length ^ n + 1) ≤ upper * ratio ^ n) :
    ∃ error : ℝ, ∀ᶠ radius : ℕ in atTop, 0 < response radius ∧
      |Real.log (response radius) - (Real.log ratio / Real.log (length : ℝ)) * Real.log (radius : ℝ)| ≤ error := by
  have hlengthReal : (1 : ℝ) < length := by exact_mod_cast hlength
  obtain ⟨offset, hoffset⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlengthReal).eventually
    (eventually_ge_atTop ((bound : ℝ) + 1))).exists
  have hoffsetNat : bound + 1 ≤ length ^ offset := by exact_mod_cast hoffset
  have hupperLevel (n : ℕ) (hn : offset ≤ n) : response (length ^ n) ≤ (upper / ratio ^ offset) * ratio ^ n := by
    have hpowerOne : 1 ≤ length ^ (n - offset) := Nat.one_le_pow _ _ (by omega)
    have hposition : bound * length ^ (n - offset) + 1 ≤ length ^ n := by
      calc
        _ ≤ (bound + 1) * length ^ (n - offset) := by nlinarith
        _ ≤ length ^ offset * length ^ (n - offset) := Nat.mul_le_mul_right _ hoffsetNat
        _ = length ^ n := by rw [← pow_add, Nat.add_sub_of_le hn]
    calc
      _ ≤ response (bound * length ^ (n - offset) + 1) := hanti hposition
      _ ≤ upper * ratio ^ (n - offset) := hupperBound _
      _ = _ := by
        rw [show n = (n - offset) + offset from (Nat.sub_add_cancel hn).symm, pow_add]
        field_simp
        simp only [Nat.add_sub_cancel]
  refine ⟨|Real.log (lower * ratio)| + |Real.log (upper / ratio ^ offset)| +
    |Real.log ratio / Real.log (length : ℝ)| * Real.log (length : ℝ), ?_⟩
  filter_upwards [eventually_ge_atTop (length ^ offset), eventually_gt_atTop 0] with radius hlarge hpositive
  have hlevel : offset ≤ Nat.log length radius := Nat.le_log_of_pow_le hlength hlarge
  have hlo := Nat.pow_log_le_self length (by omega : radius ≠ 0)
  have hhi := (Nat.lt_pow_succ_log_self hlength radius).le
  have hresponseLower : (lower * ratio) * ratio ^ Nat.log length radius ≤ response radius := by
    have hh := (hlowerBound (Nat.log length radius + 1)).trans (hanti hhi)
    simpa only [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hh
  have hresponseUpper := (hanti hlo).trans (hupperLevel _ hlevel)
  refine ⟨(mul_pos (mul_pos hlower hratio) (pow_pos hratio _)).trans_le hresponseLower, ?_⟩
  exact spatial_geometric_log_error _ _ _ _ _ _ (Nat.log length radius)
    (by exact_mod_cast hpositive) hlengthReal hratio (mul_pos hlower hratio)
    (div_pos hupper (pow_pos hratio _)) (by exact_mod_cast hlo) (by exact_mod_cast hhi)
    hresponseLower hresponseUpper

end
end Universality
