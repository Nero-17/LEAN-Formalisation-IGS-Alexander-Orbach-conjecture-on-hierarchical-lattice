import IGSIII34.Forms.AnchoredCore
import Mathlib.Topology.MetricSpace.Completion
import Mathlib.Topology.ContinuousMap.Algebra

/-! Finite-energy skeleton functions have unique continuous extensions.
This prevents unconstrained values outside the dense resistance skeleton.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)

include resistanceBound in
theorem finite_energy_uniformContinuous {potential : Carrier → ℝ}
    (finite : potential ∈ energyDomain endpoint conductance nonnegative) :
    UniformContinuous potential := by
  have energyNonnegative := limitingEnergy_nonnegative endpoint conductance nonnegative finite
  apply Metric.uniformContinuous_iff.mpr
  intro epsilon positive
  have denominatorPositive : 0 < limitingEnergy endpoint conductance potential + 1 := by linarith
  refine ⟨epsilon ^ 2 / (limitingEnergy endpoint conductance potential + 1),
    div_pos (sq_pos_of_pos positive) denominatorPositive, ?_⟩
  intro first second close
  have bound := resistanceBound potential finite first second
  have multiplied := mul_lt_mul_of_pos_right close denominatorPositive
  rw [div_mul_cancel₀ _ denominatorPositive.ne'] at multiplied
  rw [Real.dist_eq]
  nlinarith [sq_abs (potential first - potential second), abs_nonneg (potential first - potential second),
    dist_nonneg (x := first) (y := second)]

def completionExtension (potential : energyDomain endpoint conductance nonnegative) :
    C(UniformSpace.Completion Carrier, ℝ) :=
  ⟨UniformSpace.Completion.extension potential.val, UniformSpace.Completion.continuous_extension⟩

include resistanceBound in
theorem completionExtension_coe (potential : energyDomain endpoint conductance nonnegative)
    (point : Carrier) : completionExtension endpoint conductance nonnegative potential point = potential.val point :=
  UniformSpace.Completion.extension_coe
    (finite_energy_uniformContinuous endpoint conductance nonnegative resistanceBound potential.property) point

def completionExtensionLinear : (energyDomain endpoint conductance nonnegative) →ₗ[ℝ]
    C(UniformSpace.Completion Carrier, ℝ) where
  toFun := completionExtension endpoint conductance nonnegative
  map_add' first second := by
    apply DFunLike.coe_injective
    apply (UniformSpace.Completion.denseRange_coe (α := Carrier)).equalizer
      (completionExtension endpoint conductance nonnegative (first + second)).continuous
      ((completionExtension endpoint conductance nonnegative first).continuous.add
        (completionExtension endpoint conductance nonnegative second).continuous)
    funext point
    change completionExtension endpoint conductance nonnegative (first + second) (point : UniformSpace.Completion Carrier) =
      completionExtension endpoint conductance nonnegative first (point : UniformSpace.Completion Carrier) +
        completionExtension endpoint conductance nonnegative second (point : UniformSpace.Completion Carrier)
    rw [completionExtension_coe endpoint conductance nonnegative resistanceBound,
      completionExtension_coe endpoint conductance nonnegative resistanceBound,
      completionExtension_coe endpoint conductance nonnegative resistanceBound]
    rfl
  map_smul' scalar potential := by
    apply DFunLike.coe_injective
    apply (UniformSpace.Completion.denseRange_coe (α := Carrier)).equalizer
      (completionExtension endpoint conductance nonnegative (scalar • potential)).continuous
      ((completionExtension endpoint conductance nonnegative potential).continuous.const_smul scalar)
    funext point
    change completionExtension endpoint conductance nonnegative (scalar • potential) (point : UniformSpace.Completion Carrier) =
      scalar * completionExtension endpoint conductance nonnegative potential (point : UniformSpace.Completion Carrier)
    rw [completionExtension_coe endpoint conductance nonnegative resistanceBound,
      completionExtension_coe endpoint conductance nonnegative resistanceBound]
    rfl

theorem completionExtensionLinear_injective :
    Function.Injective (completionExtensionLinear endpoint conductance nonnegative resistanceBound) := by
  intro first second equal
  apply Subtype.ext
  funext point
  have equalAt := congrArg (fun function : C(UniformSpace.Completion Carrier, ℝ) =>
    function (point : UniformSpace.Completion Carrier)) equal
  change completionExtension endpoint conductance nonnegative first point =
    completionExtension endpoint conductance nonnegative second point at equalAt
  simpa only [completionExtension_coe endpoint conductance nonnegative resistanceBound] using equalAt

include resistanceBound in
theorem completionExtension_resistance (potential : energyDomain endpoint conductance nonnegative)
    (first second : UniformSpace.Completion Carrier) :
    (completionExtension endpoint conductance nonnegative potential first -
      completionExtension endpoint conductance nonnegative potential second) ^ 2 ≤
        dist first second * limitingEnergy endpoint conductance potential.val := by
  refine UniformSpace.Completion.induction_on₂ first second ?_ ?_
  · apply isClosed_le
    · exact (((completionExtension endpoint conductance nonnegative potential).continuous.comp continuous_fst).sub
        ((completionExtension endpoint conductance nonnegative potential).continuous.comp continuous_snd)).pow 2
    · exact continuous_dist.mul continuous_const
  · intro first second
    rw [completionExtension_coe endpoint conductance nonnegative resistanceBound,
      completionExtension_coe endpoint conductance nonnegative resistanceBound,
      UniformSpace.Completion.dist_eq]
    exact resistanceBound potential.val potential.property first second

end
end IGSIII34.Forms
