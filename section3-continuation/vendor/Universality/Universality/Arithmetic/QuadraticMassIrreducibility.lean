import Universality.Arithmetic.IrreducibleMass
import Universality.Matrix.CriticalCharacteristic
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! The manuscript's nonsplit mass condition is equivalent to irreducibility of
the actual two-dimensional mass characteristic polynomial over Q(p). -/

namespace Universality.Section4
open Polynomial
theorem quadratic_irreducible_iff_root_not_mem
    (base : Subfield ℝ) (trace determinant : base) (root : ℝ)
    (hroot : root ^ 2 - (trace : ℝ) * root + (determinant : ℝ) = 0) :
    Irreducible (X ^ 2 - C trace * X + C determinant : base[X]) ↔ root ∉ base := by
  have hmonic : (X ^ 2 - C trace * X + C determinant : base[X]).Monic := by
    apply monic_of_natDegree_le_of_coeff_eq_one (n := 2)
    · compute_degree
    · simp
  have hannihilates :
      (aeval root) (X ^ 2 - C trace * X + C determinant : base[X]) = 0 := by
    simpa [Subfield.algebraMap_ofSubfield] using hroot
  have hintegral : IsIntegral base root := ⟨_, hmonic, hannihilates⟩
  constructor
  · intro hirreducible hmem
    have hdegree : (X ^ 2 - C trace * X + C determinant : base[X]).natDegree = 2 := by
      compute_degree <;> norm_num
    apply hirreducible.not_isRoot_of_natDegree_ne_one (by omega)
    change (X ^ 2 - C trace * X + C determinant : base[X]).eval ⟨root, hmem⟩ = 0
    simp only [eval_add, eval_sub, eval_pow, eval_mul, eval_X, eval_C]
    apply Subtype.ext
    exact hroot
  · intro hnonsplit
    rw [← nonsplit_quadratic_minpoly base trace determinant root hroot hnonsplit]
    exact minpoly.irreducible hintegral
end Universality.Section4

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Polynomial

theorem Classical.massPlane_charpoly_irreducible_iff
    {rule : Rule} (h : rule.Classical) (p : ℝ) (hp : 0 < p) (hp' : p < 1) :
    Irreducible (Matrix.charpoly (fun i j : Fin 2 =>
      (⟨massPlaneBlock (rule.network.massMatrix p) i j,
        rule.network.massPlaneBlock_mem_adjoin p i j⟩ :
        IntermediateField.adjoin ℚ {p}))) ↔
    (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal ∉
      IntermediateField.adjoin ℚ {p} := by
  obtain ⟨symmetry, hsource, htarget⟩ := h.massAdmissible.symmetric
  have hplane := rule.network.massMatrix_preservesMassPlane p symmetry hsource htarget
  have hblock := (rule.network.massPlaneBlock_pos_of_geometry hp hp'
    (h.connected _) h.scale h.cut).1
  rw [massPlane_spectralRadius _ (rule.network.massMatrix_nonneg hp.le hp'.le) hplane hblock,
    ENNReal.toReal_ofReal (positiveRoot_pos _ hblock).le, Matrix.charpoly_fin_two]
  apply Section4.quadratic_irreducible_iff_root_not_mem
    (IntermediateField.adjoin ℚ {p}).toSubfield
  simpa [Matrix.trace, Fin.sum_univ_two, Matrix.det_fin_two] using
    positiveRoot_quadratic (massPlaneBlock (rule.network.massMatrix p)) hblock
end
end Universality.Rule
#print axioms Universality.Section4.quadratic_irreducible_iff_root_not_mem
#print axioms Universality.Rule.Classical.massPlane_charpoly_irreducible_iff
