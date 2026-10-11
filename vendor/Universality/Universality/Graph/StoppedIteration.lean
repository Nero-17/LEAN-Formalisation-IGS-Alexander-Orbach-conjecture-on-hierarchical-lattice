import Mathlib.Logic.Function.Iterate

namespace Universality

/-- Stop evaluating after a fixed point is reached.  This is extensionally
equal to ordinary iteration, for every function and decidable state space. -/
def iterateUntilFixed {α : Type*} [DecidableEq α] (f : α → α) : ℕ → α → α
  | 0, x => x
  | n + 1, x => let y := f x; if y = x then x else iterateUntilFixed f n y

theorem iterateUntilFixed_eq {α : Type*} [DecidableEq α] (f : α → α)
    (n : ℕ) (x : α) : iterateUntilFixed f n x = f^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
      simp only [iterateUntilFixed]
      split <;> rename_i h
      · exact (Function.iterate_fixed h (n + 1)).symm
      · rw [ih, Function.iterate_succ_apply]

end Universality
