import Universality.Arithmetic.IrreducibleConjugation
import Universality.Percolation.CriticalField
import Universality.Percolation.ClassicalCriticalPoint

/-! The nonsplit quadratic conclusion for the actual classical graph mass
matrix. The spectral radius is identified with its positive two-state root by
the already formalised mass-plane Perron theorem. -/

namespace Universality.Rule

noncomputable section
open FiniteNetwork Matrix

theorem Classical.nonsplit_mass_integer_power_not_mem {rule : Rule}
    (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hnonsplit : (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p})
    (exponent : ℤ) (hexponent : exponent ≠ 0) :
    (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ^ exponent ∉
      IntermediateField.adjoin ℚ {p} := by
  obtain ⟨symmetry, hsource, htarget⟩ := h.massAdmissible.symmetric
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hsource htarget
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp'
    (h.connected _) h.scale h.cut).1
  rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le] at hnonsplit ⊢
  have htrace : (massPlaneBlock (rule.network.massMatrix p)).trace ∈
      IntermediateField.adjoin ℚ {p} := by
    apply (IntermediateField.adjoin ℚ {p}).sum_mem
    intro i _
    exact rule.network.massPlaneBlock_mem_adjoin p i i
  have hdeterminant : (massPlaneBlock (rule.network.massMatrix p)).det ∈
      IntermediateField.adjoin ℚ {p} := by
    rw [Matrix.det_fin_two]
    exact (IntermediateField.adjoin ℚ {p}).sub_mem
      ((IntermediateField.adjoin ℚ {p}).mul_mem
        (rule.network.massPlaneBlock_mem_adjoin p 0 0)
        (rule.network.massPlaneBlock_mem_adjoin p 1 1))
      ((IntermediateField.adjoin ℚ {p}).mul_mem
        (rule.network.massPlaneBlock_mem_adjoin p 0 1)
        (rule.network.massPlaneBlock_mem_adjoin p 1 0))
  have hsecondary : secondaryRoot (massPlaneBlock (rule.network.massMatrix p)) ^ 2 -
      (massPlaneBlock (rule.network.massMatrix p)).trace *
        secondaryRoot (massPlaneBlock (rule.network.massMatrix p)) +
      (massPlaneBlock (rule.network.massMatrix p)).det = 0 := by
    rw [← root_sum (massPlaneBlock (rule.network.massMatrix p)),
      ← root_product (massPlaneBlock (rule.network.massMatrix p)) hblock]
    ring
  exact Section4.nonsplit_quadratic_integer_power_not_mem
    (IntermediateField.adjoin ℚ {p}).toSubfield ⟨_, htrace⟩ ⟨_, hdeterminant⟩
    (positiveRoot (massPlaneBlock (rule.network.massMatrix p)))
    (secondaryRoot (massPlaneBlock (rule.network.massMatrix p)))
    (positiveRoot_quadratic _ hblock) hsecondary hnonsplit
    (positiveRoot_pos _ hblock) (abs_secondaryRoot_lt_positiveRoot _ hblock) exponent hexponent

end
end Universality.Rule
