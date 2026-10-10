import IGSIII34.Percolation.ElectricalTransfer
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd
import Mathlib.MeasureTheory.Measure.DiracProba

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork Resistance.FiniteNetwork
open IGSIII.Chemical.Substitution
open _root_.Topology
open scoped NNReal ENNReal

def electricalCellNNReal {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Fin edges → ℝ≥0) : ℝ≥0 :=
  ⟨electricalCell rule configuration (fun edge => (input edge : ℝ)),
    (network rule configuration).effectiveResistance_nonnegative_all (fun edge => (input edge.val).2)⟩

theorem electricalCellNNReal_continuous {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges) :
    Continuous (electricalCellNNReal rule configuration) := by
  apply Continuous.subtype_mk
  have inputs : Continuous (fun input : Fin edges → ℝ≥0 =>
      (⟨fun edge => (input edge : ℝ), fun edge => (input edge).2⟩ :
        {input : Fin edges → ℝ // ∀ edge, 0 ≤ input edge})) := by
    apply Continuous.subtype_mk
    exact continuous_pi (fun edge => NNReal.continuous_coe.comp (continuous_apply edge))
  exact (electricalCell_continuous_nonnegative rule configuration).comp inputs

theorem electricalCellNNReal_joint_continuous {vertices edges : ℕ}
    (rule : Universality.FiniteNetwork vertices edges) :
    Continuous (fun data : Configuration edges × (Fin edges → ℝ≥0) =>
      electricalCellNNReal rule data.1 data.2) :=
  continuous_prod_of_discrete_left.mpr (electricalCellNNReal_continuous rule)

def connectedConfigurationLaw (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    ProbabilityMeasure (Configuration rule.edges) :=
  ⟨(finiteWeightPMF (rule.network.conditionalCellWeight parameter true)
    (rule.network.conditionalCellWeight_nonneg positive.le belowOne.le true)
    (rule.network.sum_conditionalCellWeight parameter (by rwa [fixedPoint])
      (by rwa [fixedPoint]) true)).toMeasure, inferInstance⟩

def electricalInputLaw (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) :
    ProbabilityMeasure (Configuration rule.edges × (Fin rule.edges → ℝ≥0)) :=
  (connectedConfigurationLaw rule parameter positive belowOne fixedPoint).prod
    (ProbabilityMeasure.pi (fun _ : Fin rule.edges => law))

def electricalOutputLaw (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (law : ProbabilityMeasure ℝ≥0) : ProbabilityMeasure ℝ≥0 :=
  (electricalInputLaw rule parameter positive belowOne fixedPoint law).map
    (electricalCellNNReal_joint_continuous rule.network).measurable.aemeasurable

theorem electricalInputLaw_continuous (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    Continuous (electricalInputLaw rule parameter positive belowOne fixedPoint) := by
  unfold electricalInputLaw
  exact ProbabilityMeasure.continuous_prod.comp (continuous_const.prodMk
    (ProbabilityMeasure.continuous_pi.comp (continuous_pi fun _ => continuous_id)))

theorem electricalOutputLaw_continuous (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) :
    Continuous (electricalOutputLaw rule parameter positive belowOne fixedPoint) :=
  (ProbabilityMeasure.continuous_map (electricalCellNNReal_joint_continuous rule.network)).comp
    (electricalInputLaw_continuous rule parameter positive belowOne fixedPoint)

def scaledProbabilityLaw (scalar : ℝ≥0) (law : ProbabilityMeasure ℝ≥0) :
    ProbabilityMeasure ℝ≥0 :=
  ((diracProba scalar).prod law).map (continuous_fst.mul continuous_snd).measurable.aemeasurable

theorem scaledProbabilityLaw_continuous :
    Continuous (fun data : ℝ≥0 × ProbabilityMeasure ℝ≥0 => scaledProbabilityLaw data.1 data.2) :=
  (ProbabilityMeasure.continuous_map (continuous_fst.mul continuous_snd)).comp
    (ProbabilityMeasure.continuous_prod.comp
      ((continuous_diracProba.comp continuous_fst).prodMk continuous_snd))

theorem scaledProbabilityLaw_measure (scalar : ℝ≥0) (law : ProbabilityMeasure ℝ≥0) :
    (scaledProbabilityLaw scalar law : Measure ℝ≥0) =
      (law : Measure ℝ≥0).map (fun value => scalar * value) := by
  change ((Measure.dirac scalar).prod (law : Measure ℝ≥0)).map
    (fun data : ℝ≥0 × ℝ≥0 => data.1 * data.2) = _
  rw [Measure.dirac_prod, Measure.map_map
    (g := fun data : ℝ≥0 × ℝ≥0 => data.1 * data.2) (f := Prod.mk scalar)
    (measurable_fst.mul measurable_snd) measurable_prodMk_left]
  rfl

theorem scaledProbabilityLaw_moment (scalar : ℝ≥0) (law : ProbabilityMeasure ℝ≥0) (power : ℕ) :
    (∫⁻ value, (value : ℝ≥0∞) ^ power ∂(scaledProbabilityLaw scalar law : Measure ℝ≥0)) =
      (scalar : ℝ≥0∞) ^ power * ∫⁻ value, (value : ℝ≥0∞) ^ power ∂(law : Measure ℝ≥0) := by
  rw [scaledProbabilityLaw_measure, lintegral_map
    (f := fun value : ℝ≥0 => (value : ℝ≥0∞) ^ power)
    (g := fun value : ℝ≥0 => scalar * value)
    (measurable_id.coe_nnreal_ennreal.pow_const power) (measurable_const.mul measurable_id)]
  simp only [ENNReal.coe_mul, mul_pow]
  exact lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.coe_ne_top)

theorem scaledProbabilityLaw_mean (scalar : ℝ≥0) (law : ProbabilityMeasure ℝ≥0) :
    (∫ value : ℝ≥0, (value : ℝ) ∂(scaledProbabilityLaw scalar law : Measure ℝ≥0)) =
      (scalar : ℝ) * ∫ value : ℝ≥0, (value : ℝ) ∂(law : Measure ℝ≥0) := by
  rw [scaledProbabilityLaw_measure, integral_map (φ := fun value : ℝ≥0 => scalar * value)
    (f := fun value : ℝ≥0 => (value : ℝ)) (measurable_const.mul measurable_id).aemeasurable
    NNReal.continuous_coe.measurable.aestronglyMeasurable]
  simp only [NNReal.coe_mul, integral_const_mul]

end
end IGSIII34.Percolation
