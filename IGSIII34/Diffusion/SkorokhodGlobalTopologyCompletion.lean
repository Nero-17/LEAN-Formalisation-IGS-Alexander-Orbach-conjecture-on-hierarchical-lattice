import IGSIII34.Diffusion.DiscreteIntervalSkorokhodSampleCompletion
import IGSIII34.Diffusion.SkorokhodContinuousLimitCompletion
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.Topology.MetricSpace.Pseudo.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable

/-! The topology of simultaneous J1 convergence on every integer horizon.
Each coordinate uses genuine increasing time changes. This topology is
stronger than the usual local J1 topology at paths jumping at an integer
endpoint; it is deliberately named separately. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal

structure SkorokhodGlobalPathCompletion (Space : Type*) where
  toFun : ℝ≥0 → Space

instance {Space : Type*} : CoeFun (SkorokhodGlobalPathCompletion Space)
    (fun _ => ℝ≥0 → Space) := ⟨fun path => path.toFun⟩

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def skorokhodIntegerProfileCompletion
    (path : SkorokhodGlobalPathCompletion Space) (index : ℕ) :
    SkorokhodIntervalPathCompletion Space :=
  ⟨fun time => path ((index+1 : ℝ≥0) * ⟨time.val, time.property.1⟩)⟩

instance skorokhodGlobalPseudoMetricCompletion :
    PseudoMetricSpace (SkorokhodGlobalPathCompletion Space) :=
  PseudoMetricSpace.induced skorokhodIntegerProfileCompletion PiCountable.pseudoMetricSpace

instance skorokhodGlobalMeasurableCompletion :
    MeasurableSpace (SkorokhodGlobalPathCompletion Space) := borel _

instance skorokhodGlobalBorelCompletion :
    BorelSpace (SkorokhodGlobalPathCompletion Space) := ⟨rfl⟩

theorem skorokhodIntegerProfile_inducing_completion :
    Topology.IsInducing (skorokhodIntegerProfileCompletion (Space := Space)) :=
  ⟨rfl⟩

theorem skorokhodGlobal_tendsto_iff_completion
    {Index : Type*} {along : Filter Index}
    {paths : Index → SkorokhodGlobalPathCompletion Space}
    {path : SkorokhodGlobalPathCompletion Space} :
    Tendsto paths along (𝓝 path) ↔ ∀ horizon,
      Tendsto (fun index => skorokhodIntegerProfileCompletion (paths index) horizon)
        along (𝓝 (skorokhodIntegerProfileCompletion path horizon)) := by
  rw [skorokhodIntegerProfile_inducing_completion.tendsto_nhds_iff]
  exact tendsto_pi_nhds

theorem skorokhodGlobal_continuous_iff_completion
    {Domain : Type*} [TopologicalSpace Domain]
    {sample : Domain → SkorokhodGlobalPathCompletion Space} :
    Continuous sample ↔ ∀ horizon,
      Continuous (fun outcome => skorokhodIntegerProfileCompletion (sample outcome) horizon) := by
  rw [skorokhodIntegerProfile_inducing_completion.continuous_iff]
  exact continuous_pi_iff

def skorokhodGlobalFloorReconstructionCompletion
    (scale : ℝ) (values : ℕ → Space) : SkorokhodGlobalPathCompletion Space :=
  ⟨fun time => values ⌊scale * (time : ℝ)⌋₊⟩

theorem skorokhodGlobalFloorReconstruction_continuous_completion
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) :
    Continuous (skorokhodGlobalFloorReconstructionCompletion (Space := Space) scale) := by
  apply skorokhodGlobal_continuous_iff_completion.mpr
  intro horizon
  have profileIdentity : (fun values : ℕ → Space =>
      skorokhodIntegerProfileCompletion
        (skorokhodGlobalFloorReconstructionCompletion scale values) horizon) =
      (fun values : ℕ → Space =>
        skorokhodFiniteReconstructionCompletion
          (discreteIntervalFloorSelectionCompletion scale scaleNonnegative (horizon+1))
          (fun index => values index.val)) := by
    funext values
    apply congrArg SkorokhodIntervalPathCompletion.mk
    funext time
    simp only [skorokhodIntegerProfileCompletion,
      skorokhodGlobalFloorReconstructionCompletion,
      skorokhodFiniteReconstructionCompletion,
      discreteIntervalFloorSelectionCompletion, NNReal.coe_mul,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    rw [mul_assoc]
    rfl
  rw [profileIdentity]
  exact (skorokhodFiniteReconstruction_lipschitz_completion _).continuous.comp
    (continuous_pi fun index => continuous_apply index.val)

theorem skorokhodGlobalFloorReconstruction_measurable_completion
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) :
    Measurable (skorokhodGlobalFloorReconstructionCompletion (Space := Space) scale) :=
  (skorokhodGlobalFloorReconstruction_continuous_completion scale scaleNonnegative).measurable

theorem skorokhodGlobal_measurable_of_floor_limits_completion
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (scale : ℕ → ℝ) (scaleNonnegative : ∀ index, 0 ≤ scale index)
    (values : ℕ → Outcome → ℕ → Space) (valuesMeasurable : ∀ index, Measurable (values index))
    (sample : Outcome → SkorokhodGlobalPathCompletion Space)
    (convergence : ∀ outcome, Tendsto (fun index =>
      skorokhodGlobalFloorReconstructionCompletion (scale index) (values index outcome))
      atTop (𝓝 (sample outcome))) : Measurable sample := by
  exact measurable_of_tendsto_metrizable
    (fun index => (skorokhodGlobalFloorReconstruction_measurable_completion
      (scale index) (scaleNonnegative index)).comp (valuesMeasurable index))
    (tendsto_pi_nhds.mpr convergence)

end
end IGSIII34.Diffusion
