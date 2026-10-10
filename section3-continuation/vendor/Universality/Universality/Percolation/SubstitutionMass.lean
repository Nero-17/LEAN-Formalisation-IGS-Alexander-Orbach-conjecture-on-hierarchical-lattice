import Universality.Percolation.LocalMassResponse
import Universality.Percolation.FirstMoments

/-!
# The mass matrix of the actual substituted graph

The left side is defined by graph reachability on the glued vertex set and
independent configurations of its child cells.  Thus the matrix product below
is a theorem about the finite percolation experiment, not a definition of the
left-hand side.  Terminal symmetry identifies the two orientations of a
single active endpoint.
-/

namespace Universality.FiniteNetwork
noncomputable section
open Matrix

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

def substitutedConditioning (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) : Bool := by
  classical
  let crossing := decide ((R.substitutedGraph S ω).Reachable
    (Sum.inl R.source) (Sum.inl R.target))
  exact match σ with | .connected => crossing | .both | .single => !crossing

theorem substitutedConditioning_eq (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) :
    R.substitutedConditioning S σ ω = R.conditioning σ (S.coarseConfiguration ω) := by
  classical
  have hc : decide ((R.substitutedGraph S ω).Reachable
      (Sum.inl R.source) (Sum.inl R.target)) = R.crosses (S.coarseConfiguration ω) := by
    classical
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq, substitutedReachable_iff, crosses_eq_true]
  cases σ <;> simp only [substitutedConditioning, conditioning, hc]

def substitutedConditioningProbability (p : ℝ) (σ : LiveState) : ℝ :=
  ∑ ω : Fin outerEdges → Configuration innerEdges,
    if R.substitutedConditioning S σ ω then ∏ e, bernoulliWeight p (ω e) else 0

theorem substitutedConditioningProbability_eq (p : ℝ) (σ : LiveState) :
    R.substitutedConditioningProbability S p σ =
      R.conditioningProbability (S.reliability p) σ := by
  unfold substitutedConditioningProbability
  simp_rw [substitutedConditioning_eq]
  have h := S.coarse_expectation p
    (fun coarse : Configuration outerEdges => if R.conditioning σ coarse then 1 else 0)
  simpa only [mul_ite, mul_one, mul_zero, conditioningProbability] using h

def substitutedMassMatrix (p : ℝ) : Matrix LiveState LiveState ℝ :=
  fun σ τ =>
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      if R.substitutedConditioning S σ ω then
        (∏ e, bernoulliWeight p (ω e)) * R.substitutedLiveCount S σ τ ω else 0) /
    R.substitutedConditioningProbability S p σ

theorem conditionalCellResponse_ite (p : ℝ) (opened : Bool) (condition : Prop)
    [Decidable condition] (response : Configuration innerEdges → ℝ) :
    S.conditionalCellResponse p opened (fun cell => if condition then response cell else 0) =
      if condition then S.conditionalCellResponse p opened response else 0 := by
  by_cases h : condition <;> simp [h, conditionalCellResponse]

theorem substituted_mass_numerator (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (σ τ : LiveState) :
    (∑ ω : Fin outerEdges → Configuration innerEdges,
      if R.substitutedConditioning S σ ω then
        (∏ e, bernoulliWeight p (ω e)) * R.substitutedLiveCount S σ τ ω else 0) =
    ∑ coarse : Configuration outerEdges,
      if R.conditioning σ coarse then bernoulliWeight (S.reliability p) coarse *
        R.liveResponse σ coarse (fun state => S.massMatrix p state τ) else 0 := by
  classical
  simp_rw [substitutedConditioning_eq, substitutedLiveCount_eq_local, Nat.cast_sum]
  have distribute (ω : Fin outerEdges → Configuration innerEdges) :
      (if R.conditioning σ (S.coarseConfiguration ω) then
        (∏ e, bernoulliWeight p (ω e)) *
          ∑ edge, (R.localLiveCount S (S.coarseConfiguration ω) (ω edge) σ τ edge : ℝ)
       else 0) =
      ∑ edge : Fin outerEdges, (∏ e, bernoulliWeight p (ω e)) *
        (if R.conditioning σ (S.coarseConfiguration ω) then
          (R.localLiveCount S (S.coarseConfiguration ω) (ω edge) σ τ edge : ℝ) else 0) := by
    cases R.conditioning σ (S.coarseConfiguration ω) <;> simp [Finset.mul_sum]
  simp_rw [distribute]
  rw [Finset.sum_comm]
  have localExpectation (edge : Fin outerEdges) := S.coarse_cell_expectation p hpositive hless edge
    (fun coarse cell => if R.conditioning σ coarse then
      (R.localLiveCount S coarse cell σ τ edge : ℝ) else 0)
  simp_rw [localExpectation, conditionalCellResponse_ite,
    R.localLiveCount_conditional_response S p symmetry hs ht]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coarse _
  cases R.conditioning σ coarse <;> simp [liveResponse, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro edge _
  cases R.childState σ coarse edge <;> rfl

theorem substitutedMassMatrix_eq_mul (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source) :
    R.substitutedMassMatrix S p = R.massMatrix (S.reliability p) * S.massMatrix p := by
  ext σ τ
  rw [substitutedMassMatrix, substituted_mass_numerator R S p hpositive hless symmetry hs ht,
    substitutedConditioningProbability_eq]
  change R.conditionalResponse (S.reliability p) σ (fun state => S.massMatrix p state τ) = _
  rw [← R.massMatrix_mulVec_response]
  rfl

end
end Universality.FiniteNetwork
