import Mathlib.Algebra.Group.Basic

/-!
# Why scalar multiplicative invariants forget substitution order

This is a general algebraic implication.  The separate graph construction must
supply witnesses distinguished by the critical mass observable.
-/

namespace Universality

theorem multiplicative_reordering {S T : Type*} [Mul S] [CommMonoid T]
    (f : S → T) (hmul : ∀ a b, f (a * b) = f a * f b) (a b : S) :
    f ((a * a) * (b * b)) = f (((a * b) * a) * b) := by
  simp only [hmul]
  ac_rfl

/-- No family size restriction is needed: any collection of multiplicative
scalar observations agrees on the same two reordered products. -/
theorem all_multiplicative_observations_agree {S T I : Type*} [Mul S] [CommMonoid T]
    (f : I → S → T) (hmul : ∀ i a b, f i (a * b) = f i a * f i b) (a b : S) :
    (fun i => f i ((a * a) * (b * b))) =
      (fun i => f i (((a * b) * a) * b)) := by
  funext i
  exact multiplicative_reordering (f i) (hmul i) a b

theorem no_classification_by_multiplicative_observations
    {S T I C : Type*} [Mul S] [CommMonoid T]
    (observable : S → C) (a b : S)
    (hdifferent : observable ((a * a) * (b * b)) ≠
      observable (((a * b) * a) * b))
    (f : I → S → T) (hmul : ∀ i x y, f i (x * y) = f i x * f i y) :
    ¬ ∃ classify : (I → T) → C,
      ∀ s, observable s = classify (fun i => f i s) := by
  rintro ⟨classify, hclassify⟩
  apply hdifferent
  rw [hclassify, hclassify, all_multiplicative_observations_agree f hmul a b]

end Universality
