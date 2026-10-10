import Universality.Arithmetic.SixExponentialsReal
import Universality.Arithmetic.Commensurability
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finite

namespace Universality.Section4

theorem linearIndependent_logs_of_not_commensurate
    {first second : ℕ} (hfirst : 1 < first) (hsecond : 1 < second)
    (hnot : ¬ ScaleCommensurate first second) :
    LinearIndependent ℚ ![Real.log (first : ℝ), Real.log (second : ℝ)] := by
  have hlog : Real.log (first : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast hfirst))
  apply (LinearIndependent.pair_iff' hlog).mpr
  intro coefficient heq
  apply hnot
  apply ScaleCommensurate.symm
  apply rational_log_ratio_commensurate hsecond hfirst
  refine ⟨coefficient, ?_⟩
  change (coefficient : ℝ) * Real.log (first : ℝ) = Real.log (second : ℝ) at heq
  rw [← heq, mul_div_cancel_right₀ _ hlog]

theorem commensurate_of_three_independent_dimensions
    {first second : ℕ} (hfirst : 1 < first) (hsecond : 1 < second)
    (dimensions : Fin 3 → ℝ) (hindependent : LinearIndependent ℚ dimensions)
    (hfirst_algebraic : ∀ j, IsAlgebraic ℚ
      (Real.exp (Real.log (first : ℝ) * dimensions j)))
    (hsecond_algebraic : ∀ j, IsAlgebraic ℚ
      (Real.exp (Real.log (second : ℝ) * dimensions j))) :
    ScaleCommensurate first second := by
  by_contra hnot
  apply not_linearIndependent_of_algebraic_real_exponentials
    ![Real.log (first : ℝ), Real.log (second : ℝ)] dimensions
    (linearIndependent_logs_of_not_commensurate hfirst hsecond hnot) _ hindependent
  intro i j
  fin_cases i
  · exact hfirst_algebraic j
  · exact hsecond_algebraic j

/-- A finite generating family of rank at least `count` contains an independent
subfamily of that cardinality. -/
theorem exists_independent_subfamily {size count : ℕ} (values : Fin size → ℝ)
    (hrank : count ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range values))) :
    ∃ indices : Fin count → Fin size, LinearIndependent ℚ (values ∘ indices) := by
  classical
  obtain ⟨index, select, hinjective, hspan, hindependent⟩ :=
    exists_linearIndependent' ℚ values
  letI : Fintype index := Fintype.ofInjective select hinjective
  have hcard : count ≤ Fintype.card index := by
    rw [← finrank_span_eq_card hindependent, hspan]
    exact hrank
  let embedding : Fin count → index := fun i => (Fintype.equivFin index).symm (Fin.castLE hcard i)
  have hembedding : Function.Injective embedding :=
    (Fintype.equivFin index).symm.injective.comp (Fin.castLE_injective hcard)
  exact ⟨select ∘ embedding, hindependent.comp embedding hembedding⟩

theorem commensurate_of_dimension_rank
    {first second size : ℕ} (hfirst : 1 < first) (hsecond : 1 < second)
    (dimensions : Fin size → ℝ)
    (hrank : 3 ≤ Module.finrank ℚ (Submodule.span ℚ (Set.range dimensions)))
    (hfirst_algebraic : ∀ j, IsAlgebraic ℚ
      (Real.exp (Real.log (first : ℝ) * dimensions j)))
    (hsecond_algebraic : ∀ j, IsAlgebraic ℚ
      (Real.exp (Real.log (second : ℝ) * dimensions j))) :
    ScaleCommensurate first second := by
  obtain ⟨indices, hindependent⟩ := exists_independent_subfamily dimensions hrank
  exact commensurate_of_three_independent_dimensions hfirst hsecond
    (dimensions ∘ indices) hindependent
    (fun j => hfirst_algebraic (indices j))
    (fun j => hsecond_algebraic (indices j))

theorem dimension_rank_le_two_of_not_commensurate
    {first second size : ℕ} (hfirst : 1 < first) (hsecond : 1 < second)
    (dimensions : Fin size → ℝ) (hnot : ¬ ScaleCommensurate first second)
    (hfirst_algebraic : ∀ j, IsAlgebraic ℚ
      (Real.exp (Real.log (first : ℝ) * dimensions j)))
    (hsecond_algebraic : ∀ j, IsAlgebraic ℚ
      (Real.exp (Real.log (second : ℝ) * dimensions j))) :
    Module.finrank ℚ (Submodule.span ℚ (Set.range dimensions)) ≤ 2 := by
  by_contra hrank
  exact hnot (commensurate_of_dimension_rank hfirst hsecond dimensions
    (by omega) hfirst_algebraic hsecond_algebraic)

end Universality.Section4

#print axioms Universality.Section4.commensurate_of_dimension_rank
