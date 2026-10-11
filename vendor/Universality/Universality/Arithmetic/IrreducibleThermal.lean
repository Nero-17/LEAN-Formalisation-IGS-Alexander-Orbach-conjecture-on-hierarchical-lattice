import Universality.Arithmetic.IrreducibleValuations
import Universality.Arithmetic.IntegerMultiplierObstruction
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
The arithmetic no-integer-power theorem for the complete fixed-point
polynomial. Its hypotheses are independently checkable polynomial structure,
irreducibility and critical-point conditions, not the target no-power claim.
The graph parity theorem supplying nonconstant reduction remains separate.
-/

namespace Universality.Section4

open Polynomial

theorem irreducible_fixedPoint_no_nat_power
    (reliability fixedPoint : ℤ[X]) (root : ℝ)
    (hprimitive : fixedPoint.IsPrimitive)
    (hirreducible : Irreducible (fixedPoint.map (Int.castRingHom ℚ)))
    (hroot : aeval root (fixedPoint.map (Int.castRingHom ℚ)) = 0)
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ (reliability.map (Int.castRingHom ℚ)).natDegree)
    (hzero : (reliability.map (Int.castRingHom ℚ)).derivative.eval 0 = 0)
    (hone : (reliability.map (Int.castRingHom ℚ)).derivative.eval 1 = 0)
    (hresponse : 1 < aeval root (reliability.map (Int.castRingHom ℚ)).derivative)
    (hnonconstant : ∀ prime : ℕ, prime.Prime →
      (fixedPoint.map (Int.castRingHom (ZMod prime))).natDegree ≠ 0)
    (exponent : ℕ) (hexponent : 0 < exponent) (integerValue : ℕ) :
    (aeval root (reliability.map (Int.castRingHom ℚ)).derivative) ^ exponent ≠ integerValue := by
  intro hpower
  have hintegerValue : integerValue ≠ 0 := by
    intro hzero
    rw [hzero, Nat.cast_zero] at hpower
    exact (pow_pos (lt_trans zero_lt_one hresponse) exponent).ne' hpower
  have hdividesRat : fixedPoint.map (Int.castRingHom ℚ) ∣
      (reliability.map (Int.castRingHom ℚ)).derivative ^ exponent - C (integerValue : ℚ) := by
    apply irreducible_dvd_of_common_root _ _ root hirreducible hroot
    simpa only [map_sub, map_pow, aeval_C, map_natCast, Rat.cast_natCast, sub_eq_zero] using hpower
  have hdividesInt : fixedPoint ∣ reliability.derivative ^ exponent - C (integerValue : ℤ) := by
    apply (IsPrimitive.Int.dvd_iff_map_cast_dvd_map_cast fixedPoint _ hprimitive).mpr
    simpa [Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C,
      ← derivative_map] using hdividesRat
  obtain ⟨integerRoot, hintegerRoot⟩ := fixedPoint_integer_power_is_perfect_power
    reliability fixedPoint hfactor exponent integerValue hexponent hintegerValue hdividesInt hnonconstant
  have hresponseEqual : aeval root (reliability.map (Int.castRingHom ℚ)).derivative =
      (integerRoot : ℝ) := by
    apply (pow_left_inj₀ (le_of_lt (lt_trans zero_lt_one hresponse))
      (Nat.cast_nonneg integerRoot) (Nat.ne_of_gt hexponent)).mp
    rw [hpower, ← Nat.cast_pow, hintegerRoot]
  have hintegerRootLarge : 1 < integerRoot := by
    have : (1 : ℝ) < integerRoot := hresponseEqual ▸ hresponse
    exact_mod_cast this
  apply irreducible_fixedPoint_derivative_ne_integer
    (reliability.map (Int.castRingHom ℚ)) (fixedPoint.map (Int.castRingHom ℚ)) root
    hirreducible hroot ?_ hdegree hzero hone integerRoot hintegerRootLarge hresponseEqual
  simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_one]
    using congrArg (Polynomial.map (Int.castRingHom ℚ)) hfactor

theorem irreducible_fixedPoint_no_integer_power
    (reliability fixedPoint : ℤ[X]) (root : ℝ)
    (hprimitive : fixedPoint.IsPrimitive)
    (hirreducible : Irreducible (fixedPoint.map (Int.castRingHom ℚ)))
    (hroot : aeval root (fixedPoint.map (Int.castRingHom ℚ)) = 0)
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (hdegree : 2 ≤ (reliability.map (Int.castRingHom ℚ)).natDegree)
    (hzero : (reliability.map (Int.castRingHom ℚ)).derivative.eval 0 = 0)
    (hone : (reliability.map (Int.castRingHom ℚ)).derivative.eval 1 = 0)
    (hresponse : 1 < aeval root (reliability.map (Int.castRingHom ℚ)).derivative)
    (hnonconstant : ∀ prime : ℕ, prime.Prime →
      (fixedPoint.map (Int.castRingHom (ZMod prime))).natDegree ≠ 0)
    (exponent : ℕ) (hexponent : 0 < exponent) (integerValue : ℤ) :
    (aeval root (reliability.map (Int.castRingHom ℚ)).derivative) ^ exponent ≠ integerValue := by
  intro hpower
  have hintegerNonnegative : 0 ≤ integerValue := by
    have : (0 : ℝ) ≤ integerValue :=
      hpower ▸ (pow_nonneg (le_of_lt (lt_trans zero_lt_one hresponse)) exponent)
    exact_mod_cast this
  apply irreducible_fixedPoint_no_nat_power reliability fixedPoint root hprimitive hirreducible
    hroot hfactor hdegree hzero hone hresponse hnonconstant exponent hexponent integerValue.toNat
  have hcast : (integerValue.toNat : ℝ) = integerValue := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hintegerNonnegative]
  rw [hcast]
  exact hpower

end Universality.Section4

#print axioms Universality.Section4.irreducible_fixedPoint_no_integer_power
