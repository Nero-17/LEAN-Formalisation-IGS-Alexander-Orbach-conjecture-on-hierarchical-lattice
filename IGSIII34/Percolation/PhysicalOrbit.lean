import IGSIII34.Percolation.TreeLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Percolation
noncomputable section
open MeasureTheory Universality Universality.FiniteNetwork
open IGSIII.Chemical.Substitution IGSIII.Probability
open scoped NNReal ENNReal

def electricalIterationNNReal (rule : Rule)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (depth : ℕ) (address : List (Fin rule.edges)) : ℝ≥0 :=
  ⟨electricalIteration rule marks depth address,
    electricalIteration_nonnegative rule marks depth address⟩

theorem electricalIterationNNReal_measurable (rule : Rule) (depth : ℕ)
    (address : List (Fin rule.edges)) : Measurable (fun marks => electricalIterationNNReal rule marks depth address) :=
  (electricalIteration_measurable rule depth address).subtype_mk

theorem electricalCellNNReal_scale {vertices edges : ℕ}
    (network : Universality.FiniteNetwork vertices edges) (configuration : Configuration edges)
    (input : Fin edges → ℝ≥0) (scalar : ℝ≥0) :
    electricalCellNNReal network configuration (fun edge => scalar * input edge) =
      scalar * electricalCellNNReal network configuration input := by
  apply NNReal.coe_injective
  change electricalCell network configuration (fun edge => ((scalar * input edge : ℝ≥0) : ℝ)) = _
  simp only [NNReal.coe_mul]
  exact electricalCell_scale network configuration (fun edge => (input edge).property) scalar.property

def electricalOrbitScale (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) : ℕ → ℝ≥0
  | 0 => 1
  | depth + 1 => Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth)) *
      electricalOrbitScale rule parameter positive belowOne fixedPoint depth

theorem electricalOrbitScale_positive (rule : Rule) (classical : rule.Classical)
    (parameter : ℝ) (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    0 < electricalOrbitScale rule parameter positive belowOne fixedPoint depth := by
  induction depth with
  | zero => exact zero_lt_one
  | succ depth previous =>
    apply mul_pos _ previous
    apply Real.toNNReal_pos.mpr
    exact (zero_lt_one.trans (rule.network.interior_fixed_point_strictly_unstable
      parameter positive belowOne fixedPoint classical.scale)).trans_le
      (normalizedElectricalOrbit_outputMean_bounds rule classical parameter positive belowOne fixedPoint depth).1

def normalizedPhysicalResistance (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter)
    (depth : ℕ) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ≥0 :=
  (electricalOrbitScale rule parameter positive belowOne fixedPoint depth)⁻¹ *
    electricalIterationNNReal rule marks depth []

theorem normalizedPhysicalResistance_measurable (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    Measurable (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth) :=
  measurable_const.mul (electricalIterationNNReal_measurable rule depth [])

theorem normalizedPhysicalResistance_succ (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    normalizedPhysicalResistance rule parameter positive belowOne fixedPoint (depth + 1) marks =
      Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth))⁻¹ *
      electricalCellNNReal rule.network (marks ([], true))
        (fun edge => normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth
          (innovationTreeShift rule [edge] marks)) := by
  unfold normalizedPhysicalResistance
  have childEquality (edge : Fin rule.edges) :
      electricalIterationNNReal rule (innovationTreeShift rule [edge] marks) depth [] =
        electricalIterationNNReal rule marks depth [edge] := by
    apply NNReal.coe_injective
    exact by simp only [electricalIterationNNReal, electricalIteration_shift, List.append_nil]
  simp_rw [childEquality]
  rw [electricalCellNNReal_scale]
  change (Real.toNNReal _ * electricalOrbitScale rule parameter positive belowOne fixedPoint depth)⁻¹ *
    electricalCellNNReal rule.network (marks ([], true))
      (fun edge => electricalIterationNNReal rule marks depth [edge]) = _
  rw [mul_inv_rev, Real.toNNReal_inv]
  ac_rfl

theorem normalizedPhysicalResistance_law (rule : Rule) (parameter : ℝ)
    (positive : 0 < parameter) (belowOne : parameter < 1)
    (fixedPoint : rule.network.reliability parameter = parameter) (depth : ℕ) :
    (independentInnovationLaw rule parameter positive belowOne fixedPoint).map
      (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth) =
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth : Measure ℝ≥0) := by
  induction depth with
  | zero =>
    rw [normalizedElectricalOrbit_zero]
    have zero : normalizedPhysicalResistance rule parameter positive belowOne fixedPoint 0 =
        fun _ => (1 : ℝ≥0) := by
      funext marks
      apply NNReal.coe_injective
      simp [normalizedPhysicalResistance, electricalOrbitScale, electricalIterationNNReal, electricalIteration]
      rfl
    rw [zero]
    change (independentInnovationLaw rule parameter positive belowOne fixedPoint).map (fun _ => (1 : ℝ≥0)) =
      Measure.dirac (1 : ℝ≥0)
    simp
  | succ depth previous =>
    have outputLaw := innovationTree_electrical_law rule parameter positive belowOne fixedPoint
      (normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth)
      (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth)
      (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth) previous
    rw [normalizedElectricalOrbit_succ]
    change _ = (scaledProbabilityLaw
      (Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth))⁻¹)
      (electricalOutputLaw rule parameter positive belowOne fixedPoint
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth)) : Measure ℝ≥0)
    rw [scaledProbabilityLaw_measure, ← outputLaw]
    rw [Measure.map_map
      (g := fun value : ℝ≥0 => Real.toNNReal (electricalOutputMean rule parameter positive belowOne fixedPoint
        (normalizedElectricalOrbit rule parameter positive belowOne fixedPoint depth))⁻¹ * value)
      (f := fun marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges =>
        electricalCellNNReal rule.network (marks ([], true))
        (fun edge => normalizedPhysicalResistance rule parameter positive belowOne fixedPoint depth
          (innovationTreeShift rule [edge] marks)))
      (measurable_const.mul measurable_id)
      ((electricalCellNNReal_joint_continuous rule.network).measurable.comp
        ((measurable_pi_apply ([], true)).prodMk
          (measurable_pi_lambda _ (fun edge =>
            (normalizedPhysicalResistance_measurable rule parameter positive belowOne fixedPoint depth).comp
              (innovationTreeShift_measurable rule [edge])))))]
    congr 1
    funext marks
    exact normalizedPhysicalResistance_succ rule parameter positive belowOne fixedPoint depth marks

end
end IGSIII34.Percolation
