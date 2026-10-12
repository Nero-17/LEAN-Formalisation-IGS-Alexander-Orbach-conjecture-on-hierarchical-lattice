import IGSIII34.Diffusion.SkorokhodGlobalTopologyCompletion
import IGSIII34.Diffusion.SkorokhodContinuousSampleCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology NNReal ENNReal
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def skorokhodGlobalUnitCoordinateCompletion (time : ℝ≥0) :
    SkorokhodIntervalTimeCompletion :=
  ⟨(time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ), by
    have positive : 0 < (⌊(time : ℝ)⌋₊ + 1 : ℝ) := by positivity
    exact ⟨div_nonneg time.property positive.le,
      (div_le_one positive).mpr (Nat.lt_floor_add_one (time : ℝ)).le⟩⟩

def skorokhodGlobalContinuousAssemblyCompletion
    (profiles : ℕ → C(SkorokhodIntervalTimeCompletion, Space)) :
    SkorokhodGlobalPathCompletion Space :=
  ⟨fun time => profiles ⌊(time : ℝ)⌋₊ (skorokhodGlobalUnitCoordinateCompletion time)⟩

def skorokhodGlobalProfileSelectionCompletion (horizon : ℕ)
    (time : SkorokhodIntervalTimeCompletion) : Fin (horizon+2) :=
  ⟨⌊(horizon+1 : ℝ) * (time : ℝ)⌋₊, by
    have realLE : (Real.instPreorder.toLE : LE ℝ) = Real.instLE := by rfl
    have raw := mul_le_mul_of_nonneg_left time.property.2 (by positivity : 0 ≤ (horizon+1 : ℝ))
    rw [realLE] at raw
    have bound : (horizon+1 : ℝ) * (time : ℝ) ≤ (horizon+1 : ℝ) := by
      simpa only [mul_one] using raw
    have floorBound := Nat.floor_mono bound
    have floorCast : ⌊(horizon+1 : ℝ)⌋₊ = horizon+1 := by
      simpa only [Nat.cast_add, Nat.cast_one] using Nat.floor_natCast (R := ℝ) (horizon+1)
    rw [floorCast] at floorBound
    omega⟩

def skorokhodGlobalFiniteContinuousAssemblyCompletion (horizon : ℕ)
    (profiles : Fin (horizon+2) → C(SkorokhodIntervalTimeCompletion, Space)) :
    SkorokhodIntervalPathCompletion Space :=
  ⟨fun time => profiles (skorokhodGlobalProfileSelectionCompletion horizon time)
    (skorokhodGlobalUnitCoordinateCompletion
      ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩))⟩

theorem skorokhodGlobalFiniteContinuousAssembly_lipschitz_completion (horizon : ℕ) :
    LipschitzWith 1 (skorokhodGlobalFiniteContinuousAssemblyCompletion (Space := Space) horizon) := by
  apply LipschitzWith.of_edist_le
  intro first second
  apply (skorokhodJ1EDist_le_uniform_completion _ _).trans
  apply iSup_le
  intro time
  let coordinate := skorokhodGlobalProfileSelectionCompletion horizon time
  have pointBound : edist
      (first coordinate (skorokhodGlobalUnitCoordinateCompletion
        ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩)))
      (second coordinate (skorokhodGlobalUnitCoordinateCompletion
        ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩))) ≤
      edist (first coordinate) (second coordinate) := by
    rw [ContinuousMap.edist_eq_iSup]
    exact le_iSup (fun point => edist (first coordinate point) (second coordinate point))
      (skorokhodGlobalUnitCoordinateCompletion
        ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩))
  exact pointBound.trans (edist_le_pi_edist first second coordinate)

theorem skorokhodGlobalContinuousAssembly_continuous_completion :
    Continuous (skorokhodGlobalContinuousAssemblyCompletion (Space := Space)) := by
  apply skorokhodGlobal_continuous_iff_completion.mpr
  intro horizon
  have identity : (fun profiles => skorokhodIntegerProfileCompletion
      (skorokhodGlobalContinuousAssemblyCompletion (Space := Space) profiles) horizon) =
      (fun profiles : ℕ → C(SkorokhodIntervalTimeCompletion, Space) =>
        skorokhodGlobalFiniteContinuousAssemblyCompletion horizon (fun index => profiles index.val)) := by
    funext profiles
    apply congrArg SkorokhodIntervalPathCompletion.mk
    funext time
    simp only [skorokhodGlobalContinuousAssemblyCompletion,
      skorokhodGlobalFiniteContinuousAssemblyCompletion,
      skorokhodGlobalProfileSelectionCompletion, NNReal.coe_mul,
      NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
    rfl
  rw [identity]
  exact (skorokhodGlobalFiniteContinuousAssembly_lipschitz_completion horizon).continuous.comp
    (continuous_pi fun index => continuous_apply index.val)

/-- Every continuous full-time sample with measurable evaluations is
Borel measurable in the genuine all-integer-horizon J1 topology. The
proof factors through a countable product of separable continuous-path
spaces, never identifying a nonseparable J1 Borel algebra with a product
sigma algebra. -/
theorem continuousGlobalFamily_measurable_completion
    {Outcome : Type*} [MeasurableSpace Outcome]
    (sample : Outcome → ℝ≥0 → Space) (sampleContinuous : ∀ outcome, Continuous (sample outcome))
    (evaluations : ∀ time, Measurable (fun outcome => sample outcome time)) :
    Measurable (fun outcome => (⟨sample outcome⟩ : SkorokhodGlobalPathCompletion Space)) := by
  letI : MeasurableSpace C(SkorokhodIntervalTimeCompletion, Space) := borel _
  letI : BorelSpace C(SkorokhodIntervalTimeCompletion, Space) := ⟨rfl⟩
  let profiles : Outcome → ℕ → C(SkorokhodIntervalTimeCompletion, Space) := fun outcome horizon =>
    ⟨fun time => sample outcome ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩),
      (sampleContinuous outcome).comp (by fun_prop)⟩
  have profilesMeasurable : Measurable profiles := by
    apply measurable_pi_lambda
    intro horizon
    apply continuousIntervalFamily_measurable_of_evaluations_completion
    intro time
    exact evaluations ((horizon+1 : ℝ≥0) * ⟨time.val, time.property.1⟩)
  have assembled := skorokhodGlobalContinuousAssembly_continuous_completion.measurable.comp profilesMeasurable
  convert assembled using 1
  funext outcome
  apply congrArg SkorokhodGlobalPathCompletion.mk
  funext time
  change sample outcome time = sample outcome
    ((⌊(time : ℝ)⌋₊ + 1 : ℝ≥0) *
      ⟨(time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ), _⟩)
  congr 1
  apply NNReal.eq
  simp only [NNReal.coe_mul, NNReal.coe_add, NNReal.coe_natCast, NNReal.coe_one]
  change (time : ℝ) = (⌊(time : ℝ)⌋₊ + 1 : ℝ) * ((time : ℝ) / (⌊(time : ℝ)⌋₊ + 1 : ℝ))
  have nonzero : (⌊(time : ℝ)⌋₊ + 1 : ℝ) ≠ 0 := by positivity
  field_simp

def countableSkorokhodGlobalSampleCompletion (times : ℕ → ℝ≥0) (dense : DenseRange times)
    (sample : ℕ → Space) : SkorokhodGlobalPathCompletion Space :=
  ⟨countableTimeContinuousSampleCompletion times dense sample⟩

theorem countableSkorokhodGlobalSample_measurable_completion
    (times : ℕ → ℝ≥0) (dense : DenseRange times) :
    Measurable (countableSkorokhodGlobalSampleCompletion (Space := Space) times dense) :=
  continuousGlobalFamily_measurable_completion _
    (countableTimeContinuousSample_continuous_completion times dense)
    (countableTimeContinuousSample_evaluation_measurable_completion times dense)

end
end IGSIII34.Diffusion
