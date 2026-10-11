import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

namespace Universality

/-! Algebraic recovery only. The fractions below are not definitions of
physical critical exponents. Applying this module to those exponents requires
separate existence and formula theorems for their actual observables. -/

theorem recover_pivotal_from_exponent_formula (pivotal : ℝ) :
    1 / (1 / pivotal) = pivotal := by simp

theorem recover_mass_from_exponent_formulas (ambient mass pivotal : ℝ)
    (hgap : ambient - mass ≠ 0) (hpivotal : pivotal ≠ 0) :
    ((ambient - mass) / pivotal) * (mass / (ambient - mass)) / (1 / pivotal) = mass := by
  field_simp

theorem recover_ambient_from_exponent_formulas (ambient mass pivotal : ℝ)
    (hgap : ambient - mass ≠ 0) (hpivotal : pivotal ≠ 0) :
    ((ambient - mass) / pivotal) * (mass / (ambient - mass) + 1) / (1 / pivotal) = ambient := by
  field_simp
  ring

/-- Equality of the three displayed exponent formulas recovers the dimension
triple. This is the algebraic converse, not an exponent-existence theorem. -/
theorem three_exponent_formulas_injective
    (ambient₁ mass₁ pivotal₁ ambient₂ mass₂ pivotal₂ : ℝ)
    (hgap₁ : ambient₁ - mass₁ ≠ 0) (hgap₂ : ambient₂ - mass₂ ≠ 0)
    (hpivotal₁ : pivotal₁ ≠ 0) (hpivotal₂ : pivotal₂ ≠ 0)
    (hbeta : (ambient₁ - mass₁) / pivotal₁ = (ambient₂ - mass₂) / pivotal₂)
    (hnu : 1 / pivotal₁ = 1 / pivotal₂)
    (hdelta : mass₁ / (ambient₁ - mass₁) = mass₂ / (ambient₂ - mass₂)) :
    ambient₁ = ambient₂ ∧ mass₁ = mass₂ ∧ pivotal₁ = pivotal₂ := by
  have hpivotal : pivotal₁ = pivotal₂ := by
    simpa only [recover_pivotal_from_exponent_formula] using congrArg (fun x : ℝ => 1 / x) hnu
  have hmass : mass₁ = mass₂ := by
    rw [← recover_mass_from_exponent_formulas ambient₁ mass₁ pivotal₁ hgap₁ hpivotal₁,
      ← recover_mass_from_exponent_formulas ambient₂ mass₂ pivotal₂ hgap₂ hpivotal₂]
    rw [hbeta, hdelta, hnu]
  have hambient : ambient₁ = ambient₂ := by
    rw [← recover_ambient_from_exponent_formulas ambient₁ mass₁ pivotal₁ hgap₁ hpivotal₁,
      ← recover_ambient_from_exponent_formulas ambient₂ mass₂ pivotal₂ hgap₂ hpivotal₂]
    rw [hbeta, hdelta, hnu]
  exact ⟨hambient, hmass, hpivotal⟩

theorem four_exponent_formulas_eq_iff_dimensions_eq
    (ambient₁ mass₁ pivotal₁ ambient₂ mass₂ pivotal₂ : ℝ)
    (hgap₁ : ambient₁ - mass₁ ≠ 0) (hgap₂ : ambient₂ - mass₂ ≠ 0)
    (hpivotal₁ : pivotal₁ ≠ 0) (hpivotal₂ : pivotal₂ ≠ 0) :
    ((ambient₁ - mass₁) / pivotal₁ = (ambient₂ - mass₂) / pivotal₂ ∧
      1 / pivotal₁ = 1 / pivotal₂ ∧
      mass₁ / (ambient₁ - mass₁) = mass₂ / (ambient₂ - mass₂) ∧
      2 + ambient₁ - 2 * mass₁ = 2 + ambient₂ - 2 * mass₂) ↔
      ambient₁ = ambient₂ ∧ mass₁ = mass₂ ∧ pivotal₁ = pivotal₂ := by
  constructor
  · rintro ⟨hbeta, hnu, hdelta, _⟩
    exact three_exponent_formulas_injective _ _ _ _ _ _ hgap₁ hgap₂ hpivotal₁ hpivotal₂
      hbeta hnu hdelta
  · rintro ⟨hambient, hmass, hpivotal⟩
    simp only [hambient, hmass, hpivotal, and_self]

end Universality
