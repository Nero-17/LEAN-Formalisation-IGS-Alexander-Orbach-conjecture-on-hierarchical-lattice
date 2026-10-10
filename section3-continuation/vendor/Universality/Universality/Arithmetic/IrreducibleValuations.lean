import Universality.Arithmetic.IrreducibleHensel
import Universality.Arithmetic.FixedPointPolynomial
import Mathlib.RingTheory.WittVector.Complete
import Mathlib.RingTheory.WittVector.DiscreteValuationRing
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
Witt vectors provide the unramified discrete valuation ring required by the
integer-power argument. This avoids assuming an unproved local-field bridge.
-/

namespace Universality.Section4

noncomputable section
open Polynomial

variable {prime : ℕ} [Fact prime.Prime]
variable {residue : Type*} [Field residue] [CharP residue prime] [PerfectRing residue prime]

theorem witt_simple_root_lift (polynomial : (WittVector prime residue)[X])
    (root : residue)
    (hroot : polynomial.eval₂ WittVector.constantCoeff root = 0)
    (hsimple : polynomial.derivative.eval₂ WittVector.constantCoeff root ≠ 0) :
    ∃ lift : WittVector prime residue,
      polynomial.eval lift = 0 ∧ WittVector.constantCoeff lift = root := by
  obtain ⟨initial, hinitial⟩ := WittVector.constantCoeff_surjective prime root
  have hvalue : WittVector.constantCoeff (polynomial.eval initial) = 0 := by
    rw [← eval₂_at_apply, hinitial]
    exact hroot
  have hderivative : WittVector.constantCoeff (polynomial.derivative.eval initial) ≠ 0 := by
    rw [← eval₂_at_apply, hinitial]
    exact hsimple
  have hunit : IsUnit (polynomial.derivative.eval initial) :=
    WittVector.isUnit_of_coeff_zero_ne_zero _ hderivative
  obtain ⟨lift, hzero, hcongruent⟩ := simple_root_lift_of_adicComplete
    (Ideal.span {(prime : WittVector prime residue)}) polynomial initial
    ((WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mpr hvalue)
    (hunit.map (Ideal.Quotient.mk _))
  refine ⟨lift, hzero, ?_⟩
  have hresidue := (WittVector.mem_span_p_iff_coeff_zero_eq_zero _).mp hcongruent
  change WittVector.constantCoeff (lift - initial) = 0 at hresidue
  simpa only [map_sub, hinitial, sub_eq_zero] using hresidue

theorem witt_power_factorization_divisible
    (value : WittVector prime residue) (exponent integerValue : ℕ)
    (hexponent : 0 < exponent) (hintegerValue : integerValue ≠ 0)
    (hpower : value ^ exponent = (integerValue : WittVector prime residue)) :
    exponent ∣ integerValue.factorization prime := by
  obtain ⟨valuation, remaining, hremaining, hfactorization⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd hintegerValue prime (Fact.out : prime.Prime).ne_one
  have hremainingNonzero : remaining ≠ 0 := by
    intro hzero
    exact hremaining (by simp [hzero])
  have hremainingUnit : IsUnit (remaining : WittVector prime residue) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    change WittVector.constantCoeff (remaining : WittVector prime residue) ≠ 0
    rw [map_natCast]
    exact fun hzero => hremaining ((CharP.cast_eq_zero_iff residue prime remaining).mp hzero)
  obtain ⟨remainingUnit, hremainingUnit⟩ := hremainingUnit
  have hintegerNonzero : (integerValue : WittVector prime residue) ≠ 0 := by
    rw [hfactorization, Nat.cast_mul, Nat.cast_pow, ← hremainingUnit]
    exact mul_ne_zero (pow_ne_zero _ (WittVector.p_nonzero prime residue)) remainingUnit.ne_zero
  have hvalueNonzero : value ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow (Nat.ne_of_gt hexponent)] at hpower
    exact hintegerNonzero hpower.symm
  obtain ⟨valueValuation, valueUnit, hvalue⟩ := WittVector.exists_eq_pow_p_mul' value hvalueNonzero
  have hcompare : ((valueUnit ^ exponent : (WittVector prime residue)ˣ) : WittVector prime residue) *
      (prime : WittVector prime residue) ^ (valueValuation * exponent) =
      (remainingUnit : WittVector prime residue) * (prime : WittVector prime residue) ^ valuation := by
    rw [hvalue, mul_pow, ← pow_mul] at hpower
    rw [hfactorization, Nat.cast_mul, Nat.cast_pow, ← hremainingUnit] at hpower
    simpa only [Units.val_pow_eq_pow_val, mul_comm] using hpower
  have hvaluation := IsDiscreteValuationRing.unit_mul_pow_congr_pow
    (WittVector.irreducible prime) (WittVector.irreducible prime)
    (valueUnit ^ exponent) remainingUnit (valueValuation * exponent) valuation hcompare
  have hfactor : integerValue.factorization prime = valuation := by
    rw [hfactorization, Nat.factorization_mul
      (pow_ne_zero _ (Fact.out : prime.Prime).ne_zero) hremainingNonzero]
    simp only [Finsupp.add_apply, Nat.factorization_pow_self (Fact.out : prime.Prime),
      Nat.factorization_eq_zero_of_not_dvd hremaining, add_zero]
  rw [hfactor, ← hvaluation]
  exact dvd_mul_left _ _

/-- A residue root of the fixed-point polynomial lifts to a response whose
given integer power is unchanged. Its derivative is forced to be a unit by
the fixed-point identity, so the lift is proved rather than assumed. -/
theorem fixedPoint_witt_response_power
    (reliability fixedPoint : ℤ[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (exponent integerValue : ℕ)
    (hdivides : fixedPoint ∣ reliability.derivative ^ exponent - C (integerValue : ℤ))
    (hprimeDivides : prime ∣ integerValue)
    (root : residue) (hroot : fixedPoint.eval₂ (Int.castRingHom residue) root = 0) :
    ∃ value : WittVector prime residue, value ^ exponent = integerValue := by
  have hresponse := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
    (Int.castRingHom residue) root hdivides hroot
  simp only [eval₂_sub, eval₂_pow, map_natCast, eval₂_natCast,
    (CharP.cast_eq_zero_iff residue prime integerValue).mpr hprimeDivides, sub_zero] at hresponse
  have hresponseZero : reliability.derivative.eval₂ (Int.castRingHom residue) root = 0 :=
    eq_zero_of_pow_eq_zero hresponse
  have hfactorResidue : reliability.map (Int.castRingHom residue) - X =
      X * (1 - X) * fixedPoint.map (Int.castRingHom residue) := by
    simpa only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_mul, Polynomial.map_one]
      using congrArg (Polynomial.map (Int.castRingHom residue)) hfactor
  have hsimple : fixedPoint.derivative.eval₂ (Int.castRingHom residue) root ≠ 0 := by
    have h := fixedPoint_derivative_ne_zero_at_root
      (reliability.map (Int.castRingHom residue)) (fixedPoint.map (Int.castRingHom residue))
      hfactorResidue root (by simpa only [eval_map] using hroot)
      (by simpa only [derivative_map, eval_map] using hresponseZero)
    simpa only [derivative_map, eval_map] using h
  have hmaps : (WittVector.constantCoeff : WittVector prime residue →+* residue).comp
      (Int.castRingHom (WittVector prime residue)) = Int.castRingHom residue :=
    Subsingleton.elim _ _
  obtain ⟨lift, hlift, _⟩ := witt_simple_root_lift
    (fixedPoint.map (Int.castRingHom (WittVector prime residue))) root
    (by simpa only [eval₂_map, hmaps] using hroot)
    (by simpa only [derivative_map, eval₂_map, hmaps] using hsimple)
  have hliftRoot : fixedPoint.eval₂ (Int.castRingHom (WittVector prime residue)) lift = 0 := by
    simpa only [eval_map] using hlift
  refine ⟨reliability.derivative.eval₂ (Int.castRingHom (WittVector prime residue)) lift, ?_⟩
  have h := eval₂_eq_zero_of_dvd_of_eval₂_eq_zero
    (Int.castRingHom (WittVector prime residue)) lift hdivides hliftRoot
  simpa only [eval₂_sub, eval₂_pow, eval₂_C, map_natCast, eval₂_natCast,
    sub_eq_zero] using h

theorem fixedPoint_residue_root_factorization_divisible
    (reliability fixedPoint : ℤ[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (exponent integerValue : ℕ) (hexponent : 0 < exponent) (hintegerValue : integerValue ≠ 0)
    (hdivides : fixedPoint ∣ reliability.derivative ^ exponent - C (integerValue : ℤ))
    (hprimeDivides : prime ∣ integerValue)
    (root : residue) (hroot : fixedPoint.eval₂ (Int.castRingHom residue) root = 0) :
    exponent ∣ integerValue.factorization prime := by
  obtain ⟨value, hvalue⟩ := fixedPoint_witt_response_power reliability fixedPoint hfactor
    exponent integerValue hdivides hprimeDivides root hroot
  exact witt_power_factorization_divisible value exponent integerValue hexponent hintegerValue hvalue

/-- Nonconstant reduction supplies the residue root in an algebraic closure.
Together with the preceding proved lifting theorem, this gives the precise
prime-exponent divisibility claimed by the paper's local argument. -/
theorem fixedPoint_reduction_factorization_divisible
    (reliability fixedPoint : ℤ[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (exponent integerValue : ℕ) (hexponent : 0 < exponent) (hintegerValue : integerValue ≠ 0)
    (hdivides : fixedPoint ∣ reliability.derivative ^ exponent - C (integerValue : ℤ))
    (hprimeDivides : prime ∣ integerValue)
    (hnonconstant : (fixedPoint.map (Int.castRingHom (ZMod prime))).natDegree ≠ 0) :
    exponent ∣ integerValue.factorization prime := by
  let residueField := AlgebraicClosure (ZMod prime)
  have hmaps : (algebraMap (ZMod prime) residueField).comp
      (Int.castRingHom (ZMod prime)) = Int.castRingHom residueField := Subsingleton.elim _ _
  have hdegree : (fixedPoint.map (Int.castRingHom residueField)).natDegree ≠ 0 := by
    rw [← hmaps, ← Polynomial.map_map, natDegree_map]
    exact hnonconstant
  obtain ⟨root, hroot⟩ := IsAlgClosed.exists_root
    (fixedPoint.map (Int.castRingHom residueField)) (fun hzero =>
      hdegree (natDegree_eq_of_degree_eq_some hzero))
  exact fixedPoint_residue_root_factorization_divisible reliability fixedPoint hfactor
    exponent integerValue hexponent hintegerValue hdivides hprimeDivides root
    (by simpa only [Polynomial.IsRoot, eval_map] using hroot)

theorem exists_nat_power_of_factorization_divisible (integerValue exponent : ℕ)
    (hintegerValue : integerValue ≠ 0)
    (hdivides : ∀ prime, exponent ∣ integerValue.factorization prime) :
    ∃ root : ℕ, root ^ exponent = integerValue := by
  classical
  refine ⟨∏ prime ∈ integerValue.factorization.support,
    prime ^ (integerValue.factorization prime / exponent), ?_⟩
  rw [← Finset.prod_pow]
  calc
    (∏ prime ∈ integerValue.factorization.support,
      (prime ^ (integerValue.factorization prime / exponent)) ^ exponent) =
        ∏ prime ∈ integerValue.factorization.support, prime ^ integerValue.factorization prime := by
      apply Finset.prod_congr rfl
      intro prime _
      rw [← pow_mul, Nat.div_mul_cancel (hdivides prime)]
    _ = integerValue := Nat.prod_factorization_pow_eq_self hintegerValue

theorem fixedPoint_integer_power_is_perfect_power
    (reliability fixedPoint : ℤ[X])
    (hfactor : reliability - X = X * (1 - X) * fixedPoint)
    (exponent integerValue : ℕ) (hexponent : 0 < exponent) (hintegerValue : integerValue ≠ 0)
    (hdivides : fixedPoint ∣ reliability.derivative ^ exponent - C (integerValue : ℤ))
    (hnonconstant : ∀ prime : ℕ, prime.Prime →
      (fixedPoint.map (Int.castRingHom (ZMod prime))).natDegree ≠ 0) :
    ∃ root : ℕ, root ^ exponent = integerValue := by
  apply exists_nat_power_of_factorization_divisible integerValue exponent hintegerValue
  intro prime
  by_cases hprime : prime.Prime
  · by_cases hprimeDivides : prime ∣ integerValue
    · letI : Fact prime.Prime := ⟨hprime⟩
      exact fixedPoint_reduction_factorization_divisible reliability fixedPoint hfactor
        exponent integerValue hexponent hintegerValue hdivides hprimeDivides (hnonconstant prime hprime)
    · rw [Nat.factorization_eq_zero_of_not_dvd hprimeDivides]
      exact dvd_zero _
  · rw [Nat.factorization_eq_zero_of_not_prime integerValue hprime]
    exact dvd_zero _

end
end Universality.Section4
