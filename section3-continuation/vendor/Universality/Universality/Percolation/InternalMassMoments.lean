import Universality.Percolation.InternalMassSymmetry
import Universality.Probability.FiniteProductMoments

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def conditionalInternalMoment (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) (r : ℕ) : ℝ :=
  ∑ configuration, R.conditionalCellWeight p opened configuration *
    (R.internalSelectedMass sourceSelected targetSelected configuration : ℝ) ^ r

theorem conditionalInternalMoment_one (R : FiniteNetwork vertices edges) (p : ℝ)
    (opened sourceSelected targetSelected : Bool) :
    R.conditionalInternalMoment p opened sourceSelected targetSelected 1 =
      R.conditionalInternalMean p opened sourceSelected targetSelected := by
  simp only [conditionalInternalMoment, pow_one, conditionalInternalMean]

theorem conditionalInternalMoment_zero (R : FiniteNetwork vertices edges) (p : ℝ)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) :
    R.conditionalInternalMoment p opened sourceSelected targetSelected 0 = 1 := by
  simp only [conditionalInternalMoment, pow_zero, mul_one]
  exact R.sum_conditionalCellWeight p hpositive hless opened

theorem conditionalInternalMoment_nonneg (R : FiniteNetwork vertices edges) (p : ℝ)
    (hp : 0 ≤ p) (hp' : p ≤ 1) (opened sourceSelected targetSelected : Bool) (r : ℕ) :
    0 ≤ R.conditionalInternalMoment p opened sourceSelected targetSelected r :=
  Finset.sum_nonneg (fun configuration _ => mul_nonneg
    (R.conditionalCellWeight_nonneg hp hp' opened configuration) (pow_nonneg (Nat.cast_nonneg _) r))

theorem NetworkSymmetry.conditionalInternalMoment_swap {R : FiniteNetwork vertices edges}
    (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (opened sourceSelected targetSelected : Bool) (r : ℕ) :
    R.conditionalInternalMoment p opened sourceSelected targetSelected r =
      R.conditionalInternalMoment p opened targetSelected sourceSelected r := by
  unfold conditionalInternalMoment
  rw [← symmetry.configurationEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro configuration _
  rw [symmetry.conditionalCellWeight R hs ht,
    symmetry.internalSelectedMass_configuration hs ht]

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

/-- Exact higher-moment identity, with the reward kept inside the sum over
the coarse configuration that also determines every child type. -/
theorem conditionalInternalMoment_substitute (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (opened sourceSelected targetSelected : Bool) (r : ℕ) :
    (R.substitute S).conditionalInternalMoment p opened sourceSelected targetSelected r =
      ∑ coarse, R.conditionalCellWeight (S.reliability p) opened coarse *
        ∑ k ∈ Finset.range (r + 1),
          (R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) ^ (r - k) *
            (r.choose k : ℝ) *
          ∑ assignment : Fin k → Fin outerEdges, ∏ edge,
            S.conditionalInternalMoment p (coarse edge)
              (R.orientedChildState sourceSelected targetSelected coarse edge).sourceSelected
              (R.orientedChildState sourceSelected targetSelected coarse edge).targetSelected
              (Fintype.card {a : Fin k // assignment a = edge}) := by
  unfold conditionalInternalMoment
  rw [← substitutionConfigurationEquiv.sum_comp]
  simp_rw [R.internalSelectedMass_substitute S, Nat.cast_add, Nat.cast_sum]
  rw [R.conditional_substitution_observable S p hpositive hless opened
    (fun coarse cells => ((R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) +
      ∑ edge, (S.internalStateMass
        (R.orientedChildState sourceSelected targetSelected coarse edge) (cells edge) : ℝ)) ^ r)]
  apply Finset.sum_congr rfl
  intro coarse _
  congr 1
  simpa only [internalStateMass] using finite_product_reward_sum_moment
    (fun edge cell => S.conditionalCellWeight p (coarse edge) cell)
    (fun edge cell => (S.internalStateMass
      (R.orientedChildState sourceSelected targetSelected coarse edge) cell : ℝ))
    (R.internalSelectedMass sourceSelected targetSelected coarse : ℝ) r

end
end Universality.FiniteNetwork
