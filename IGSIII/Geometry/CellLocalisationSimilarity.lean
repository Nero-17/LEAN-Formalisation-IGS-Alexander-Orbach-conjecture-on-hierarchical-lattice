import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.UniformSpace.Equiv

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace IGSIII.Geometry
noncomputable section
open UniformSpace

variable {First Last : Type*} [MetricSpace First] [MetricSpace Last]

/-- An actual bijection of dense metric skeletons with a positive distance
factor extends canonically to a bijection of their full completions. -/
def completionSimilarity (equivalence : First ≃ Last) (factor : ℝ) (factorPositive : 0 < factor)
    (distanceScaled : ∀ first last, dist (equivalence first) (equivalence last) = factor * dist first last) :
    Completion First ≃ᵤ Completion Last := by
  have forwardLipschitz : LipschitzWith ⟨factor, factorPositive.le⟩ equivalence :=
    LipschitzWith.of_dist_le_mul (fun first last => (distanceScaled first last).le)
  have inverseLipschitz : LipschitzWith ⟨factor⁻¹, inv_nonneg.mpr factorPositive.le⟩ equivalence.symm := by
    apply LipschitzWith.of_dist_le_mul
    intro first last
    have identity := distanceScaled (equivalence.symm first) (equivalence.symm last)
    simp only [Equiv.apply_symm_apply] at identity
    change dist (equivalence.symm first) (equivalence.symm last) ≤ factor⁻¹ * dist first last
    rw [identity, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt factorPositive), one_mul]
  exact Completion.mapEquiv
    { toEquiv := equivalence
      uniformContinuous_toFun := forwardLipschitz.uniformContinuous
      uniformContinuous_invFun := inverseLipschitz.uniformContinuous }

@[simp] theorem completionSimilarity_coe (equivalence : First ≃ Last) (factor : ℝ) (factorPositive : 0 < factor)
    (distanceScaled : ∀ first last, dist (equivalence first) (equivalence last) = factor * dist first last)
    (point : First) : completionSimilarity equivalence factor factorPositive distanceScaled point = (equivalence point : Completion Last) :=
  Completion.mapEquiv_coe _ _

theorem completionSimilarity_distance (equivalence : First ≃ Last) (factor : ℝ) (factorPositive : 0 < factor)
    (distanceScaled : ∀ first last, dist (equivalence first) (equivalence last) = factor * dist first last)
    (first last : Completion First) :
    dist (completionSimilarity equivalence factor factorPositive distanceScaled first)
      (completionSimilarity equivalence factor factorPositive distanceScaled last) = factor * dist first last := by
  have continuousSimilarity := (completionSimilarity equivalence factor factorPositive distanceScaled).uniformContinuous.continuous
  refine Completion.induction_on₂ first last (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro first last
  simpa only [completionSimilarity_coe, Completion.dist_eq] using distanceScaled first last

end
end IGSIII.Geometry
