import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Exact commensurability of discrete scales

Commensurability means equality after positive integral blocking.  The prime
valuation argument below proves that the scales used in the infinite family
are pairwise incommensurate.  Existence of the associated graph rules is a
separate certificate theorem, not assumed here.
-/

namespace Universality

def ScaleCommensurate (a b : ℕ) : Prop :=
  ∃ m n : ℕ, 0 < m ∧ 0 < n ∧ a ^ m = b ^ n

theorem ScaleCommensurate.refl (a : ℕ) : ScaleCommensurate a a :=
  ⟨1, 1, by decide, by decide, rfl⟩

theorem ScaleCommensurate.symm {a b : ℕ} (h : ScaleCommensurate a b) :
    ScaleCommensurate b a := by
  obtain ⟨m, n, hm, hn, heq⟩ := h
  exact ⟨n, m, hn, hm, heq.symm⟩

theorem ScaleCommensurate.trans {a b c : ℕ}
    (hab : ScaleCommensurate a b) (hbc : ScaleCommensurate b c) :
    ScaleCommensurate a c := by
  obtain ⟨m, n, hm, hn, hmn⟩ := hab
  obtain ⟨p, q, hp, hq, hpq⟩ := hbc
  refine ⟨m * p, q * n, Nat.mul_pos hm hp, Nat.mul_pos hq hn, ?_⟩
  calc
    a ^ (m * p) = (a ^ m) ^ p := by rw [pow_mul]
    _ = (b ^ n) ^ p := by rw [hmn]
    _ = (b ^ p) ^ n := by rw [← pow_mul, ← pow_mul, Nat.mul_comm n p]
    _ = (c ^ q) ^ n := by rw [hpq]
    _ = c ^ (q * n) := by rw [pow_mul]

theorem ScaleCommensurate.of_powers {a b r s : ℕ}
    (hr : 0 < r) (hs : 0 < s) (h : ScaleCommensurate (a ^ r) (b ^ s)) :
    ScaleCommensurate a b := by
  obtain ⟨m, n, hm, hn, heq⟩ := h
  exact ⟨r * m, s * n, Nat.mul_pos hr hm, Nat.mul_pos hs hn,
    by simpa only [pow_mul] using heq⟩

theorem prime_family_index_eq {p q i j : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (h : ScaleCommensurate (p * q ^ i) (p * q ^ j)) : i = j := by
  obtain ⟨m, n, hm, hn, heq⟩ := h
  have hpval := congrArg (fun x : ℕ => x.factorization p) heq
  have hqval := congrArg (fun x : ℕ => x.factorization q) heq
  have hqp : q ≠ p := Ne.symm hpq
  simp [Nat.factorization_pow, Nat.factorization_mul hp.ne_zero (pow_ne_zero _ hq.ne_zero),
    hp.factorization, hq.factorization, hpq, hqp] at hpval hqval
  subst n
  exact Nat.eq_of_mul_eq_mul_left hm hqval

theorem explicit_scales_pairwise_incommensurate {i j : ℕ} (hij : i ≠ j) :
    ¬ ScaleCommensurate ((19 * 661 ^ i) ^ 100) ((19 * 661 ^ j) ^ 100) := by
  intro h
  apply hij
  exact prime_family_index_eq (by norm_num) (by norm_num) (by norm_num)
    (h.of_powers (by norm_num) (by norm_num))

theorem commensurate_log_ratio {a b : ℕ} (_ha : 1 < a) (hb : 1 < b)
    (h : ScaleCommensurate a b) :
    ∃ q : ℚ, Real.log (a : ℝ) / Real.log (b : ℝ) = q := by
  obtain ⟨m, n, hm, hn, heq⟩ := h
  refine ⟨(n : ℚ) / m, ?_⟩
  have hreal : (a : ℝ) ^ m = (b : ℝ) ^ n := by exact_mod_cast heq
  have hlog := congrArg Real.log hreal
  rw [Real.log_pow, Real.log_pow] at hlog
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hb0 : Real.log (b : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hb))
  push_cast
  apply (div_eq_div_iff hb0 hm0).mpr
  nlinarith

theorem rational_log_ratio_commensurate {a b : ℕ} (ha : 1 < a) (hb : 1 < b)
    (h : ∃ q : ℚ, Real.log (a : ℝ) / Real.log (b : ℝ) = q) :
    ScaleCommensurate a b := by
  obtain ⟨q, hq⟩ := h
  have ha' : 1 < (a : ℝ) := by exact_mod_cast ha
  have hb' : 1 < (b : ℝ) := by exact_mod_cast hb
  have hqpos : (0 : ℝ) < q := by
    rw [← hq]
    exact div_pos (Real.log_pos ha') (Real.log_pos hb')
  have hqrat : 0 < q := by exact_mod_cast hqpos
  have hnumpos : 0 < q.num := Rat.num_pos.mpr hqrat
  have habs : (q.num.natAbs : ℝ) = (q.num : ℝ) := by
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ))
      (Int.natAbs_of_nonneg hnumpos.le)
  have hnpos : 0 < q.num.natAbs := by
    have hnumreal : (0 : ℝ) < q.num := by exact_mod_cast hnumpos
    rw [← habs] at hnumreal
    exact_mod_cast hnumreal
  refine ⟨q.den, q.num.natAbs, q.den_pos, hnpos, ?_⟩
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  rw [Rat.cast_def, ← habs] at hq
  have hlogs := (div_eq_div_iff (ne_of_gt (Real.log_pos hb')) hden).mp hq
  have hpowers : (a : ℝ) ^ q.den = (b : ℝ) ^ q.num.natAbs := by
    apply Real.log_injOn_pos (pow_pos (lt_trans zero_lt_one ha') _) 
      (pow_pos (lt_trans zero_lt_one hb') _)
    rw [Real.log_pow, Real.log_pow]
    nlinarith
  exact_mod_cast hpowers

theorem commensurate_iff_rational_log_ratio {a b : ℕ} (ha : 1 < a) (hb : 1 < b) :
    ScaleCommensurate a b ↔
      ∃ q : ℚ, Real.log (a : ℝ) / Real.log (b : ℝ) = q :=
  ⟨commensurate_log_ratio ha hb, rational_log_ratio_commensurate ha hb⟩

end Universality
