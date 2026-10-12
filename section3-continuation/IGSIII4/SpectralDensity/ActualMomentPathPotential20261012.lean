import IGSIII4.SpectralDensity.ActualMomentOhmic20261012
import Mathlib.Data.Fin.Basic

set_option autoImplicit false

namespace IGSIII4.SpectralDensity
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

def pathPrefixOpen {length : ℕ} (configuration : Fin length → Bool)
    (position : Fin (length + 1)) : Prop :=
  ∀ edge : Fin length, edge.val < position.val → configuration edge = true

def pathSuffixOpen {length : ℕ} (configuration : Fin length → Bool)
    (position : Fin (length + 1)) : Prop :=
  ∀ edge : Fin length, position.val ≤ edge.val → configuration edge = true

def failedPathPotential {length : ℕ} (configuration : Fin length → Bool)
    (left right : ℝ) (position : Fin (length + 1)) : ℝ :=
  if pathPrefixOpen configuration position then left
  else if pathSuffixOpen configuration position then right else 0

theorem pathPrefixOpen_step20261012 {length : ℕ} (configuration : Fin length → Bool)
    (edge : Fin length) (opened : configuration edge = true) :
    pathPrefixOpen configuration edge.castSucc ↔ pathPrefixOpen configuration edge.succ := by
  constructor
  · intro initialOpen earlier before
    by_cases same : earlier = edge
    · subst earlier; exact opened
    · exact initialOpen earlier (by have := Fin.val_ne_of_ne same; simp only [Fin.val_castSucc, Fin.val_succ] at *; omega)
  · intro initialOpen earlier before
    exact initialOpen earlier (by simp only [Fin.val_castSucc, Fin.val_succ] at *; omega)

theorem pathSuffixOpen_step20261012 {length : ℕ} (configuration : Fin length → Bool)
    (edge : Fin length) (opened : configuration edge = true) :
    pathSuffixOpen configuration edge.castSucc ↔ pathSuffixOpen configuration edge.succ := by
  constructor
  · intro suffix later after
    exact suffix later (by simp only [Fin.val_castSucc, Fin.val_succ] at *; omega)
  · intro suffix later after
    by_cases same : later = edge
    · subst later; exact opened
    · exact suffix later (by have := Fin.val_ne_of_ne same; simp only [Fin.val_castSucc, Fin.val_succ] at *; omega)

/-- Every dangling open fragment has constant voltage, including isolated middle fragments. -/
theorem failedPathPotential_open_edge20261012 {length : ℕ}
    (configuration : Fin length → Bool) (left right : ℝ)
    (edge : Fin length) (opened : configuration edge = true) :
    failedPathPotential configuration left right edge.castSucc =
      failedPathPotential configuration left right edge.succ := by
  simp only [failedPathPotential,
    pathPrefixOpen_step20261012 configuration edge opened,
    pathSuffixOpen_step20261012 configuration edge opened]

theorem failedPathPotential_left20261012 {length : ℕ}
    (configuration : Fin length → Bool) (left right : ℝ) :
    failedPathPotential configuration left right 0 = left := by
  simp [failedPathPotential, pathPrefixOpen]

theorem failedPathPotential_right20261012 {length : ℕ}
    (configuration : Fin length → Bool) (left right : ℝ)
    (failed : ¬∀ edge, configuration edge = true) :
    failedPathPotential configuration left right (Fin.last length) = right := by
  have noPrefix : ¬pathPrefixOpen configuration (Fin.last length) := by
    intro initialOpen
    exact failed (fun edge => initialOpen edge edge.isLt)
  have suffix : pathSuffixOpen configuration (Fin.last length) := by
    intro edge after
    have := edge.isLt
    simp only [Fin.val_last] at after
    omega
  simp only [failedPathPotential, noPrefix, ↓reduceIte, suffix]

def pathPrefixResistance {length : ℕ} (resistance : Fin length → ℝ)
    (position : Fin (length + 1)) : ℝ :=
  ∑ edge, if edge.val < position.val then resistance edge else 0

theorem pathPrefixResistance_step20261012 {length : ℕ} (resistance : Fin length → ℝ)
    (edge : Fin length) :
    pathPrefixResistance resistance edge.succ =
      pathPrefixResistance resistance edge.castSucc + resistance edge := by
  have pointwise (other : Fin length) :
      (if other.val < edge.succ.val then resistance other else 0) =
        (if other.val < edge.castSucc.val then resistance other else 0) +
          (if other = edge then resistance edge else 0) := by
    by_cases same : other = edge
    · subst other; simp
    · have different := Fin.val_ne_of_ne same
      have comparison : other.val < edge.succ.val ↔ other.val < edge.castSucc.val := by
        simp only [Fin.val_succ, Fin.val_castSucc]
        omega
      simp only [comparison, same, ↓reduceIte, add_zero]
  simp only [pathPrefixResistance, pointwise, Finset.sum_add_distrib]
  simp

theorem pathPrefixResistance_left20261012 {length : ℕ} (resistance : Fin length → ℝ) :
    pathPrefixResistance resistance 0 = 0 := by
  simp [pathPrefixResistance]

theorem pathPrefixResistance_right20261012 {length : ℕ} (resistance : Fin length → ℝ) :
    pathPrefixResistance resistance (Fin.last length) = ∑ edge, resistance edge := by
  simp [pathPrefixResistance]

def conductingPathPotential {length : ℕ} (resistance : Fin length → ℝ)
    (current left : ℝ) (position : Fin (length + 1)) : ℝ :=
  left - current * pathPrefixResistance resistance position

theorem conductingPathPotential_ohm20261012 {length : ℕ} (resistance : Fin length → ℝ)
    (current left : ℝ) (edge : Fin length) :
    conductingPathPotential resistance current left edge.castSucc -
        conductingPathPotential resistance current left edge.succ = resistance edge * current := by
  simp only [conductingPathPotential, pathPrefixResistance_step20261012]
  ring

def openPathPotential {length : ℕ} (configuration : Fin length → Bool)
    (resistance : Fin length → ℝ) (current left right : ℝ)
    (position : Fin (length + 1)) : ℝ :=
  if ∀ edge, configuration edge = true then
    conductingPathPotential resistance current left position
  else failedPathPotential configuration left right position

theorem openPathPotential_left20261012 {length : ℕ} (configuration : Fin length → Bool)
    (resistance : Fin length → ℝ) (current left right : ℝ) :
    openPathPotential configuration resistance current left right 0 = left := by
  unfold openPathPotential
  split_ifs
  · simp [conductingPathPotential, pathPrefixResistance_left20261012]
  · exact failedPathPotential_left20261012 configuration left right

theorem openPathPotential_right20261012 {length : ℕ} (configuration : Fin length → Bool)
    (resistance : Fin length → ℝ) (current left right : ℝ)
    (voltage : (∀ edge, configuration edge = true) →
      current * (∑ edge, resistance edge) = left - right) :
    openPathPotential configuration resistance current left right (Fin.last length) = right := by
  unfold openPathPotential
  split_ifs with complete
  · simp only [conductingPathPotential, pathPrefixResistance_right20261012, voltage complete]
    ring
  · exact failedPathPotential_right20261012 configuration left right complete

theorem openPathPotential_ohm20261012 {length : ℕ} (configuration : Fin length → Bool)
    (resistance : Fin length → ℝ) (current left right : ℝ)
    (zeroWhenFailed : (¬∀ edge, configuration edge = true) → current = 0)
    (edge : Fin length) (opened : configuration edge = true) :
    openPathPotential configuration resistance current left right edge.castSucc -
      openPathPotential configuration resistance current left right edge.succ =
        resistance edge * current := by
  unfold openPathPotential
  split_ifs with complete
  · exact conductingPathPotential_ohm20261012 resistance current left edge
  · rw [zeroWhenFailed complete, mul_zero,
      failedPathPotential_open_edge20261012 configuration left right edge opened, sub_self]

end
end IGSIII4.SpectralDensity
