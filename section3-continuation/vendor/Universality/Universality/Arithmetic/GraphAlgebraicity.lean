import Universality.Arithmetic.GraphAlgebraicHelpers
import Universality.Percolation.CriticalField
import Universality.Percolation.ClassicalCriticalPoint

/-!
# Algebraicity of actual finite graph responses

The fixed-point equation below is the reliability polynomial of the actual
Bernoulli graph experiment.  The mass matrix is the actual conditional counting
matrix, and eigenvalues are members of mathlib's complex spectrum.
-/

namespace Universality.FiniteNetwork
noncomputable section
open Polynomial IntermediateField

variable {vertices edges : ℕ} (network : FiniteNetwork vertices edges)

theorem reliabilityPolynomial_sub_X_ne_zero
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    network.reliabilityPolynomial - X ≠ 0 := by
  intro hzero
  have hpolynomial : network.reliabilityPolynomial = X := sub_eq_zero.mp hzero
  have hderivative := (network.hasDerivAt_reliability 0).deriv
  rw [hpolynomial, Polynomial.derivative_X] at hderivative
  have hvanishing := network.derivative_zero_zero hscale
  norm_num at hderivative
  linarith

theorem fixed_point_isAlgebraic (p : ℝ)
    (hfixed : network.reliability p = p)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    IsAlgebraic ℚ p := by
  refine ⟨network.reliabilityPolynomial - X,
    network.reliabilityPolynomial_sub_X_ne_zero hscale, ?_⟩
  change (network.reliabilityPolynomial - X).eval₂ (Rat.castHom ℝ) p = 0
  rw [Polynomial.eval₂_sub, network.reliabilityPolynomial_eval, Polynomial.eval₂_X,
    hfixed, sub_self]

theorem reliability_deriv_mem_field (field : IntermediateField ℚ ℝ)
    {p : ℝ} (hp : p ∈ field) : deriv network.reliability p ∈ field := by
  rw [(network.hasDerivAt_reliability p).deriv]
  exact Section4.polynomial_eval_mem_field field hp network.reliabilityPolynomial.derivative

theorem reliability_deriv_mem_adjoin (p : ℝ) :
    deriv network.reliability p ∈ ℚ⟮p⟯ :=
  network.reliability_deriv_mem_field _ (mem_adjoin_simple_self ℚ p)

theorem reliability_deriv_isAlgebraic {p : ℝ} (hp : IsAlgebraic ℚ p) :
    IsAlgebraic ℚ (deriv network.reliability p) := by
  apply mem_algebraicClosure_iff.mp
  exact network.reliability_deriv_mem_field (algebraicClosure ℚ ℝ)
    (mem_algebraicClosure_iff.mpr hp)

theorem massMatrix_entry_isAlgebraic {p : ℝ} (hp : IsAlgebraic ℚ p)
    (sourceState targetState : LiveState) :
    IsAlgebraic ℚ (network.massMatrix p sourceState targetState) := by
  apply mem_algebraicClosure_iff.mp
  exact network.massMatrix_mem_field (algebraicClosure ℚ ℝ)
    (mem_algebraicClosure_iff.mpr hp) sourceState targetState

theorem massMatrix_eigenvalue_isAlgebraic {p : ℝ} (hp : IsAlgebraic ℚ p)
    {eigenvalue : ℂ}
    (heigenvalue : eigenvalue ∈ spectrum ℂ ((network.massMatrix p).map Complex.ofReal)) :
    IsAlgebraic ℚ eigenvalue := by
  apply Section4.isAlgebraic_matrix_spectrum _ _ heigenvalue
  intro sourceState targetState
  exact (network.massMatrix_entry_isAlgebraic hp sourceState targetState).algHom
    (IsScalarTower.toAlgHom ℚ ℝ ℂ)

/-- The algebraicity lemma needs only an actual fixed point and terminal
distance greater than one, so in particular applies to every admissible rule.
Simplicity, canonicality and symmetry are not needed for this statement. -/
theorem fixed_point_responses_algebraic (p : ℝ)
    (hfixed : network.reliability p = p)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    IsAlgebraic ℚ p ∧
      IsAlgebraic ℚ (deriv network.reliability p) ∧
      (∀ sourceState targetState,
        IsAlgebraic ℚ (network.massMatrix p sourceState targetState)) ∧
      (∀ eigenvalue ∈ spectrum ℂ ((network.massMatrix p).map Complex.ofReal),
        IsAlgebraic ℚ eigenvalue) := by
  have hp := network.fixed_point_isAlgebraic p hfixed hscale
  exact ⟨hp, network.reliability_deriv_isAlgebraic hp,
    network.massMatrix_entry_isAlgebraic hp,
    fun _ heigenvalue => network.massMatrix_eigenvalue_isAlgebraic hp heigenvalue⟩

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix

/-- The paper's algebraicity lemma, including every complex eigenvalue of the
actual three-state matrix, at any interior critical point of a classical rule. -/
theorem Classical.critical_responses_algebraic {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hfixed : rule.network.reliability p = p) :
    IsAlgebraic ℚ p ∧
      IsAlgebraic ℚ (deriv rule.network.reliability p) ∧
      (∀ sourceState targetState,
        IsAlgebraic ℚ (rule.network.massMatrix p sourceState targetState)) ∧
      (∀ eigenvalue ∈ spectrum ℂ ((rule.network.massMatrix p).map Complex.ofReal),
        IsAlgebraic ℚ eigenvalue) := by
  exact rule.network.fixed_point_responses_algebraic p hfixed h.scale

/-- A positive eigenvector for the actual spectral radius of a classical rule. -/
theorem Classical.mass_spectralRadius_positive_eigenvector {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ∧
      ∃ weight : LiveState → ℝ, (∀ state, 0 < weight state) ∧
        rule.network.massMatrix p *ᵥ weight =
          (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • weight := by
  obtain ⟨symmetry, hsource, htarget⟩ := h.massAdmissible.symmetric
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hsource htarget
  obtain ⟨hblock, _⟩ := rule.network.massPlaneBlock_pos_of_geometry hp hp'
    (h.connected _) h.scale h.cut
  have hpositive := positiveRoot_pos (massPlaneBlock (rule.network.massMatrix p)) hblock
  have hvector : ∀ state, 0 < massPlaneLift
      ![massPlaneBlock (rule.network.massMatrix p) 0 1,
        positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          massPlaneBlock (rule.network.massMatrix p) 0 0] state := by
    apply massPlaneLift_pos
    intro i
    fin_cases i
    · exact hblock 0 1
    · exact positiveRoot_sub_diagonal_pos _ hblock
  have heigenvector : rule.network.massMatrix p *ᵥ massPlaneLift
      ![massPlaneBlock (rule.network.massMatrix p) 0 1,
        positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          massPlaneBlock (rule.network.massMatrix p) 0 0] =
      positiveRoot (massPlaneBlock (rule.network.massMatrix p)) • massPlaneLift
      ![massPlaneBlock (rule.network.massMatrix p) 0 1,
        positiveRoot (massPlaneBlock (rule.network.massMatrix p)) -
          massPlaneBlock (rule.network.massMatrix p) 0 0] := by
    rw [hplane, positiveRoot_eigenvector _ hblock, massPlaneLift_smul]
  rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal hpositive.le]
  exact ⟨hpositive, _, hvector, heigenvector⟩

/-- The actual Perron growth factor is algebraic; the proof identifies it with
a positive eigenvalue rather than assuming algebraicity of spectral radius. -/
theorem Classical.mass_spectralRadius_isAlgebraic {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) :
    IsAlgebraic ℚ ((spectralRadius ℂ
      ((rule.network.massMatrix p).map Complex.ofReal)).toReal) := by
  obtain ⟨_, weight, hweight, heigenvector⟩ :=
    h.mass_spectralRadius_positive_eigenvector p hp hp'
  have hcomplex := rule.network.massMatrix_eigenvalue_isAlgebraic
    (rule.network.fixed_point_isAlgebraic p hfixed h.scale)
    (mem_spectrum_of_positive_eigenvector _ weight _ hweight heigenvector)
  exact (isAlgebraic_algHom_iff (IsScalarTower.toAlgHom ℚ ℝ ℂ)
    (IsScalarTower.toAlgHom ℚ ℝ ℂ).injective).mp hcomplex

end
end Universality.Rule

#print axioms Universality.FiniteNetwork.fixed_point_isAlgebraic
#print axioms Universality.FiniteNetwork.fixed_point_responses_algebraic
#print axioms Universality.Rule.Classical.critical_responses_algebraic
#print axioms Universality.Rule.Classical.mass_spectralRadius_isAlgebraic
