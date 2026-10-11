import Universality.Arithmetic.Commensurability

namespace Universality.Section4

/-- A primitive integer base is an integer greater than one which is not a
proper integral power. -/
def PrimitiveIntegerBase (base : ℕ) : Prop :=
  1 < base ∧ ∀ root exponent : ℕ, 1 < exponent → base ≠ root ^ exponent

theorem exists_primitive_integer_base (scale : ℕ) (hscale : 1 < scale) :
    ∃ base : ℕ, PrimitiveIntegerBase base ∧
      ∃ exponent : ℕ, 0 < exponent ∧ scale = base ^ exponent := by
  classical
  have hexists : ∃ base : ℕ, 1 < base ∧
      ∃ exponent : ℕ, 0 < exponent ∧ scale = base ^ exponent :=
    ⟨scale, hscale, 1, by decide, by simp⟩
  obtain ⟨hbase, exponent, hexponent, hpower⟩ := Nat.find_spec hexists
  refine ⟨Nat.find hexists, ⟨hbase, ?_⟩, exponent, hexponent, hpower⟩
  intro root power hpower_gt hroot
  have hroot_gt : 1 < root := by
    by_contra h
    have hle := pow_le_pow_left' (Nat.le_of_not_gt h) power
    rw [one_pow, ← hroot] at hle
    exact (not_le_of_gt hbase) hle
  have hminimal : Nat.find hexists ≤ root := Nat.find_min' hexists
    ⟨hroot_gt, power * exponent, Nat.mul_pos (lt_trans zero_lt_one hpower_gt) hexponent,
      by rw [hpower, hroot, pow_mul]⟩
  have hlt : root < Nat.find hexists := by
    rw [hroot]
    exact lt_self_pow₀ hroot_gt hpower_gt
  exact (not_le_of_gt hlt) hminimal

theorem commensurate_with_primitive_base_iff
    {base scale : ℕ} (hbase : PrimitiveIntegerBase base) (hscale : 1 < scale) :
    ScaleCommensurate base scale ↔
      ∃ exponent : ℕ, 0 < exponent ∧ scale = base ^ exponent := by
  constructor
  · rintro ⟨left, right, hleft, hright, heq⟩
    obtain ⟨root, hbase_root, hscale_root⟩ :=
      Nat.exists_eq_pow_of_pow_eq_pow (Or.inl (Nat.ne_of_gt hleft)) heq
    have hpower_ne : right / Nat.gcd left right ≠ 0 := by
      intro hzero
      rw [hzero, pow_zero] at hbase_root
      exact (ne_of_gt hbase.1) hbase_root
    have hpower_one : right / Nat.gcd left right = 1 := by
      by_contra h
      have hgt : 1 < right / Nat.gcd left right :=
        lt_of_le_of_ne (Nat.one_le_iff_ne_zero.mpr hpower_ne) (Ne.symm h)
      exact hbase.2 root _ hgt hbase_root
    have hroot : base = root := by simpa only [hpower_one, pow_one] using hbase_root
    have hexponent : 0 < left / Nat.gcd left right := by
      apply Nat.pos_of_ne_zero
      intro hzero
      rw [hzero, pow_zero] at hscale_root
      exact (ne_of_gt hscale) hscale_root
    exact ⟨_, hexponent, by simpa only [← hroot] using hscale_root⟩
  · rintro ⟨exponent, hexponent, hpower⟩
    exact ⟨exponent, 1, hexponent, by decide, by simpa only [pow_one] using hpower.symm⟩

/-- One primitive base works simultaneously for an arbitrary nonempty family
of pairwise commensurate integer scales. No finiteness assumption is needed. -/
theorem common_primitive_integer_base {ι : Type*} [Nonempty ι]
    (scales : ι → ℕ) (hscales : ∀ i, 1 < scales i)
    (hcommensurate : ∀ i j, ScaleCommensurate (scales i) (scales j)) :
    ∃ base : ℕ, PrimitiveIntegerBase base ∧
      ∀ i, ∃ exponent : ℕ, 0 < exponent ∧ scales i = base ^ exponent := by
  classical
  obtain ⟨reference⟩ := ‹Nonempty ι›
  obtain ⟨base, hbase, exponent, hexponent, hpower⟩ :=
    exists_primitive_integer_base (scales reference) (hscales reference)
  refine ⟨base, hbase, fun i => (commensurate_with_primitive_base_iff hbase (hscales i)).mp ?_⟩
  have hreference : ScaleCommensurate base (scales reference) :=
    (commensurate_with_primitive_base_iff hbase (hscales reference)).mpr
      ⟨exponent, hexponent, hpower⟩
  exact hreference.trans (hcommensurate reference i)

end Universality.Section4

#print axioms Universality.Section4.common_primitive_integer_base
