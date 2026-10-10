import Mathlib.Analysis.Complex.Exponential
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.RingTheory.Algebraic.Defs

/-!
# Accepted external six exponentials theorem

This is the standard complex six exponentials theorem, quoted as
`thm:six-exponentials` in Section 4 of the manuscript (Dasgupta, 2021,
Introduction to Transcendence Theory, Lecture 1). The user explicitly accepted
this external theorem on 2026-10-06; proving it is outside this formalisation.
Its mathematical dependency remains visible in every downstream axiom audit.
No percolation or Section 4 conclusion is assumed here.
-/

namespace Universality.External

/-- The accepted six exponentials theorem, with rational linear independence
in each of the two complex families. -/
axiom six_exponentials (first : Fin 2 → ℂ) (second : Fin 3 → ℂ)
    (hfirst : LinearIndependent ℚ first)
    (hsecond : LinearIndependent ℚ second) :
    ∃ i j, Transcendental ℚ (Complex.exp (first i * second j))

end Universality.External

namespace Universality.Section4

theorem not_linearIndependent_of_algebraic_exponentials
    (first : Fin 2 → ℂ) (second : Fin 3 → ℂ)
    (hfirst : LinearIndependent ℚ first)
    (halgebraic : ∀ i j, IsAlgebraic ℚ (Complex.exp (first i * second j))) :
    ¬ LinearIndependent ℚ second := by
  intro hsecond
  obtain ⟨i, j, htranscendental⟩ := External.six_exponentials first second hfirst hsecond
  exact htranscendental (halgebraic i j)

end Universality.Section4

#print axioms Universality.Section4.not_linearIndependent_of_algebraic_exponentials
