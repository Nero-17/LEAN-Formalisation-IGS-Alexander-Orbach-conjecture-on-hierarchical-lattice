import IGSIII34.Diffusion.DiscreteIntervalSkorokhodSampleCompletion20261011
import IGSIII34.Diffusion.SkorokhodContinuousLimitCompletion20261011
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

structure SkorokhodGlobalPathCompletion20261011 (Space : Type*) where
  toFun : ℝ≥0 → Space

instance {Space : Type*} : CoeFun (SkorokhodGlobalPathCompletion20261011 Space)
    (fun _ => ℝ≥0 → Space) := ⟨fun path => path.toFun⟩

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def skorokhodIntegerProfileCompletion20261011
    (path : SkorokhodGlobalPathCompletion20261011 Space) (index : ℕ) :
    SkorokhodIntervalPathCompletion20261011 Space :=
  ⟨fun time => path ((index+1 : ℝ≥0) * ⟨time.val, time.property.1⟩)⟩

instance skorokhodGlobalPseudoMetricCompletion20261011 :
    PseudoMetricSpace (SkorokhodGlobalPathCompletion20261011 Space) :=
  PseudoMetricSpace.induced skorokhodIntegerProfileCompletion20261011 PiCountable.pseudoMetricSpace

instance skorokhodGlobalMeasurableCompletion20261011 :
    MeasurableSpace (SkorokhodGlobalPathCompletion20261011 Space) := borel _

instance skorokhodGlobalBorelCompletion20261011 :
    BorelSpace (SkorokhodGlobalPathCompletion20261011 Space) := ⟨rfl⟩

theorem skorokhodIntegerProfile_inducing_completion20261011 :
    Topology.IsInducing (skorokhodIntegerProfileCompletion20261011 (Space := Space)) :=
  ⟨rfl⟩

theorem skorokhodGlobal_tendsto_iff_completion20261011
    {Index : Type*} {along : Filter Index}
    {paths : Index → SkorokhodGlobalPathCompletion20261011 Space}
    {path : SkorokhodGlobalPathCompletion20261011 Space} :
    Tendsto paths along (𝓝 path) ↔ ∀ horizon,
      Tendsto (fun index => skorokhodIntegerProfileCompletion20261011 (paths index) horizon)
        along (𝓝 (skorokhodIntegerProfileCompletion20261011 path horizon)) := by
  rw [skorokhodIntegerProfile_inducing_completion20261011.tendsto_nhds_iff]
  exact tendsto_pi_nhds

theorem skorokhodGlobal_continuous_iff_completion20261011
    {Domain : Type*} [TopologicalSpace Domain]
    {sample : Domain → SkorokhodGlobalPathCompletion20261011 Space} :
    Continuous sample ↔ ∀ horizon,
      Continuous (fun outcome => skorokhodIntegerProfileCompletion20261011 (sample outcome) horizon) := by
  rw [skorokhodIntegerProfile_inducing_completion20261011.continuous_iff]
  exact continuous_pi_iff

def skorokhodGlobalFloorReconstructionCompletion20261011
    (scale : ℝ) (values : ℕ → Space) : SkorokhodGlobalPathCompletion20261011 Space :=
  ⟨fun time => values ⌊scale * (time : ℝ)⌋₊⟩

theorem skorokhodGlobalFloorReconstruction_continuous_completion20261011
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) :
    Continuous (skorokhodGlobalFloorReconstructionCompletion20261011 (Space := Space) scale) := by
  apply skorokhodGlobal_continuous_iff_completion20261011.mpr
  intro horizon
  have profileIdentity : (fun values : ℕ → Space =>
      skorokhodIntegerProfileCompletion20261011
        (skorokhodGlobalFloorReconstructionCompletion20261011 scale values) horizon) =
      (fun values : ℕ → Space =>
        skorokhodFiniteReconstructionCompletion20261011
          (discreteIntervalFloorSelectionCompletion20261011 scale scaleNonnegative (horizon+1))
          (fun index => values index.val)) := by
    funext values
    apply congrArg SkorokhodIntervalPathCompletion20261011.mk
    funext time
    simp only [skorokhodIntegerProfileCompletion20261011,
      skorokhodGlobalFloorReconstructionCompletion20261011,
      skorokhodFiniteReconstructionCompletion20261011,
      discreteIntervalFloorSelectionCompletion20261011, NNReal.coe_mul,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    rw [mul_assoc]
    rfl
  rw [profileIdentity]
  exact (skorokhodFiniteReconstruction_lipschitz_completion20261011 _).continuous.comp
    (continuous_pi fun index => continuous_apply index.val)

theorem skorokhodGlobalFloorReconstruction_measurable_completion20261011
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    (scale : ℝ) (scaleNonnegative : 0 ≤ scale) :
    Measurable (skorokhodGlobalFloorReconstructionCompletion20261011 (Space := Space) scale) :=
  (skorokhodGlobalFloorReconstruction_continuous_completion20261011 scale scaleNonnegative).measurable

theorem skorokhodGlobal_measurable_of_floor_limits_completion20261011
    [MeasurableSpace Space] [BorelSpace Space] [SecondCountableTopology Space]
    {Outcome : Type*} [MeasurableSpace Outcome]
    (scale : ℕ → ℝ) (scaleNonnegative : ∀ index, 0 ≤ scale index)
    (values : ℕ → Outcome → ℕ → Space) (valuesMeasurable : ∀ index, Measurable (values index))
    (sample : Outcome → SkorokhodGlobalPathCompletion20261011 Space)
    (convergence : ∀ outcome, Tendsto (fun index =>
      skorokhodGlobalFloorReconstructionCompletion20261011 (scale index) (values index outcome))
      atTop (𝓝 (sample outcome))) : Measurable sample := by
  exact measurable_of_tendsto_metrizable
    (fun index => (skorokhodGlobalFloorReconstruction_measurable_completion20261011
      (scale index) (scaleNonnegative index)).comp (valuesMeasurable index))
    (tendsto_pi_nhds.mpr convergence)

end
end IGSIII34.Diffusion
