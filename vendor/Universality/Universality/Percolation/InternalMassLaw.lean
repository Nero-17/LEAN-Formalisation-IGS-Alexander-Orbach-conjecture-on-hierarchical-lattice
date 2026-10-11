import Universality.Percolation.InternalVertexMass
import Universality.Percolation.ConditionalSubstitutionLaw

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def conditionalInternalMean (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) : ℝ :=
  ∑ ω, R.conditionalCellWeight p opened ω * R.internalSelectedMass sourceSelected targetSelected ω

/-- The finite probability-generating polynomial evaluated at a real argument;
the coefficients are probabilities of actual internal vertex masses. -/
def conditionalInternalPGF (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (z : ℝ) : ℝ :=
  ∑ ω, R.conditionalCellWeight p opened ω * z ^ R.internalSelectedMass sourceSelected targetSelected ω

theorem conditionalInternalPGF_one (R : FiniteNetwork vertices edges) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) :
    R.conditionalInternalPGF p opened sourceSelected targetSelected 1 = 1 := by
  simp only [conditionalInternalPGF, one_pow, mul_one]
  exact R.sum_conditionalCellWeight p hpositive hless opened

theorem conditionalInternalMean_nonneg (R : FiniteNetwork vertices edges) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (opened sourceSelected targetSelected : Bool) :
    0 ≤ R.conditionalInternalMean p opened sourceSelected targetSelected := by
  apply Finset.sum_nonneg
  intro ω _
  exact mul_nonneg (R.conditionalCellWeight_nonneg hp hp' opened ω) (Nat.cast_nonneg _)

theorem conditionalInternalPGF_inactive (R : FiniteNetwork vertices edges) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened : Bool) (z : ℝ) :
    R.conditionalInternalPGF p opened false false z = 1 := by
  simp only [conditionalInternalPGF, internalSelectedMass, selectedActive,
    Bool.false_and, Bool.false_or, Bool.false_eq_true, ↓reduceIte,
    Finset.sum_const_zero, pow_zero, mul_one]
  exact R.sum_conditionalCellWeight p hpositive hless opened

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- The exact first-moment recursion at arbitrary parameters. The top-level
reward is sampled with the offspring configuration, not independently. -/
theorem conditionalInternalMean_substitute (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) :
    (R.substitute S).conditionalInternalMean p opened sourceSelected targetSelected =
      ∑ coarse, R.conditionalCellWeight (S.reliability p) opened coarse *
        ((R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) +
          ∑ e, S.conditionalInternalMean p (coarse e)
            (R.orientedChildState sourceSelected targetSelected coarse e).sourceSelected
            (R.orientedChildState sourceSelected targetSelected coarse e).targetSelected) := by
  unfold conditionalInternalMean
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.internalSelectedMass_substitute S, Nat.cast_add, Nat.cast_sum]
  rw [R.conditional_substitution_observable S p hpositive hless opened
    (fun coarse cells => (R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) +
      ∑ e, (S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e)
        (cells e) : ℝ))]
  apply Finset.sum_congr rfl
  intro coarse _
  rw [S.conditional_product_additive_response p hpositive hless coarse
    (R.internalSelectedMass sourceSelected targetSelected coarse : ℝ)
    (fun e cell => (S.internalStateMass
      (R.orientedChildState sourceSelected targetSelected coarse e) cell : ℝ))]
  rfl

/-- Full distribution recursion, not merely a moment identity. Each product
factor corresponds to an independently conditioned child cell, while the
joint offspring types and reward share one coarse configuration. -/
theorem conditionalInternalPGF_substitute (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) (z : ℝ) :
    (R.substitute S).conditionalInternalPGF p opened sourceSelected targetSelected z =
      ∑ coarse, R.conditionalCellWeight (S.reliability p) opened coarse *
        z ^ R.internalSelectedMass sourceSelected targetSelected coarse *
          ∏ e, S.conditionalInternalPGF p (coarse e)
            (R.orientedChildState sourceSelected targetSelected coarse e).sourceSelected
            (R.orientedChildState sourceSelected targetSelected coarse e).targetSelected z := by
  unfold conditionalInternalPGF
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.internalSelectedMass_substitute S]
  rw [R.conditional_substitution_observable S p hpositive hless opened
    (fun coarse cells => z ^ (R.internalSelectedMass sourceSelected targetSelected coarse +
      ∑ e, S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) (cells e)))]
  apply Finset.sum_congr rfl
  intro coarse _
  rw [mul_assoc]
  congr 1
  simp only [pow_add, ← Finset.prod_pow_eq_pow_sum]
  have hfactor (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ e, S.conditionalCellWeight p (coarse e) (cells e)) *
        (z ^ R.internalSelectedMass sourceSelected targetSelected coarse *
          ∏ e, z ^ S.internalStateMass
            (R.orientedChildState sourceSelected targetSelected coarse e) (cells e)) =
      z ^ R.internalSelectedMass sourceSelected targetSelected coarse *
        ∏ e, S.conditionalCellWeight p (coarse e) (cells e) *
          z ^ S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) (cells e) := by
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [internalStateMass] using (Fintype.prod_sum
    (fun e cell => S.conditionalCellWeight p (coarse e) cell *
      z ^ S.internalStateMass (R.orientedChildState sourceSelected targetSelected coarse e) cell)).symm

end
end Universality.FiniteNetwork
