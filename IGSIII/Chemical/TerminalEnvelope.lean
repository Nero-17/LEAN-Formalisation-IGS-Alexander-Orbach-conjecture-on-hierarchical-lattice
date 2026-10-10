import IGSIII.Chemical.OrbitSupremumMoments
import IGSIII.Geometry.MarkedComponentRadii

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork MeasureTheory IGSIII.Probability IGSIII.Geometry
open IGSIII.Chemical.SmallBall
open scoped ENNReal

noncomputable def chemicalTerminalEnvelope (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened : Bool)
    (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) : ℝ :=
  if opened then ⨆ depth,
    chemicalOrbit rule p positive belowOne fixedPoint growth depth (innovationTreeShift rule address marks)
  else 0

theorem chemicalTerminalEnvelope_measurable (rule : Rule)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
    (address : List (Fin rule.edges)) (opened : Bool) :
    Measurable (chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth address opened) := by
  cases opened with
  | false => exact measurable_const
  | true =>
    apply Measurable.iSup
    intro depth
    exact (Lp.stronglyMeasurable (chemicalOrbit rule p positive belowOne fixedPoint growth depth)).measurable.comp
      (innovationTreeShift_measurable rule address)

theorem chemicalTerminalEnvelope_moments_and_bound_of_orbit_supremum
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) (growth : ℝ) (growthPositive : 0 < growth)
    (order : ℝ≥0∞)
    (supremumMemLp : MemLp
      (fun marks => ⨆ depth, chemicalOrbit rule p positive belowOne fixedPoint growth depth marks)
        order (independentInnovationLaw rule p positive belowOne fixedPoint))
    (supremumBounds : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ depth,
      chemicalOrbit rule p positive belowOne fixedPoint growth depth marks ≤
        ⨆ index, chemicalOrbit rule p positive belowOne fixedPoint growth index marks) :
    (∀ address opened, MemLp (chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth address opened)
      order (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
    (∀ address opened, eLpNorm (chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth address opened)
      order (independentInnovationLaw rule p positive belowOne fixedPoint) ≤
        eLpNorm (fun marks => ⨆ depth, chemicalOrbit rule p positive belowOne fixedPoint growth depth marks)
          order (independentInnovationLaw rule p positive belowOne fixedPoint)) ∧
    ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address opened depth,
      (markedTerminalDistance rule marks depth address opened : ℝ) / growth ^ (depth + 1) ≤
        chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth address opened marks := by
  constructor
  · intro address opened
    cases opened with
    | false => exact memLp_const (0 : ℝ)
    | true =>
      exact supremumMemLp.comp_measurePreserving
        (innovationTreeShift_preserving rule p positive belowOne fixedPoint address)
  constructor
  · intro address opened
    cases opened with
    | false =>
      change eLpNorm (0 : (((List (Fin rule.edges) × Bool) → Configuration rule.edges) → ℝ))
        order (independentInnovationLaw rule p positive belowOne fixedPoint) ≤ _
      rw [eLpNorm_zero]
      exact bot_le
    | true =>
      have identity := eLpNorm_comp_measurePreserving
        (p := order)
        (g := fun marks => ⨆ depth, chemicalOrbit rule p positive belowOne fixedPoint growth depth marks)
        (f := innovationTreeShift rule address) supremumMemLp.aestronglyMeasurable
        (innovationTreeShift_preserving rule p positive belowOne fixedPoint address)
      exact identity.le
  · have shiftedBounds : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address depth,
          chemicalOrbit rule p positive belowOne fixedPoint growth depth (innovationTreeShift rule address marks) ≤
            ⨆ index, chemicalOrbit rule p positive belowOne fixedPoint growth index (innovationTreeShift rule address marks) :=
      ae_all_iff.mpr (fun address =>
        (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae supremumBounds)
    have shiftedValues : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint,
        ∀ address depth,
          chemicalOrbit rule p positive belowOne fixedPoint growth depth (innovationTreeShift rule address marks) =
            growth⁻¹ ^ depth * ((chemicalTransfer rule)^[depth] (fun _ => 1)) (innovationTreeShift rule address marks) := by
      apply ae_all_iff.mpr
      intro address
      have rootValues : ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ depth,
          chemicalOrbit rule p positive belowOne fixedPoint growth depth marks = growth⁻¹ ^ depth *
            ((chemicalTransfer rule)^[depth] (fun _ => 1)) marks :=
        ae_all_iff.mpr (fun depth => normalizedChemicalTransferLp_iterate_ae rule p positive belowOne fixedPoint
          2 growth growthPositive.le depth)
      exact (innovationTreeShift_preserving rule p positive belowOne fixedPoint address).quasiMeasurePreserving.ae rootValues
    filter_upwards [independentInnovationLaw_crosses rule p positive belowOne fixedPoint, shiftedBounds, shiftedValues,
      chemicalTransfer_iterate_eq_actual_ae rule classical.simple p positive belowOne fixedPoint]
      with marks crossing bounds values actual
    intro address opened depth
    cases opened with
    | false => simp [markedTerminalDistance_noncrossing rule marks crossing, chemicalTerminalEnvelope]
    | true =>
      have identity := values address (depth + 1)
      rw [actual depth address] at identity
      have ratioIdentity : growth⁻¹ ^ (depth + 1) *
          (((rule.generation depth).network.openGraph (markedGenerationConfiguration rule marks depth address true)).dist
            (rule.generation depth).network.source (rule.generation depth).network.target : ℝ) =
          (markedTerminalDistance rule marks depth address true : ℝ) / growth ^ (depth + 1) := by
        unfold markedTerminalDistance
        rw [inv_pow]
        ring
      rw [ratioIdentity] at identity
      exact identity ▸ bounds address (depth + 1)

theorem exists_actual_chemical_terminal_envelope
    (rule : Rule) (classical : rule.Classical)
    (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p) :
    ∃ constant growth : ℝ, 0 < constant ∧ constant ≤ 1 ∧
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ≤ growth ∧
      growth ≤ longestTerminalPath rule.network ∧
      (∀ depth, growth ^ depth ≤ manuscriptDistanceMean rule p depth ∧
        manuscriptDistanceMean rule p depth ≤ constant⁻¹ * growth ^ depth) ∧
      (∀ order : ℝ≥0∞, 1 ≤ order → order ≠ ∞ → ∃ bound : ℝ≥0∞, bound ≠ ∞ ∧
        ∀ address opened,
          MemLp (chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth address opened)
            order (independentInnovationLaw rule p positive belowOne fixedPoint) ∧
          eLpNorm (chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth address opened)
            order (independentInnovationLaw rule p positive belowOne fixedPoint) ≤ bound) ∧
      ∀ᵐ marks ∂independentInnovationLaw rule p positive belowOne fixedPoint, ∀ address opened depth,
        (markedTerminalDistance rule marks depth address opened : ℝ) / growth ^ (depth + 1) ≤
          chemicalTerminalEnvelope rule p positive belowOne fixedPoint growth address opened marks := by
  obtain ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds,
    value, valueFixed, valuePositive, _, _, lower, upper, lowerPositive, upperPositive, comparison⟩ :=
    exists_actual_positive_endogenous_chemical_field rule classical p positive belowOne fixedPoint
  have growthPositive : 0 < growth :=
    lt_of_lt_of_le (by exact_mod_cast Nat.zero_lt_of_lt classical.scale) growthLower
  have supremumProperties (order : ℝ≥0∞) [Fact (1 ≤ order)] (orderFinite : order ≠ ∞) :=
    chemicalOrbit_supremum_memLp_of_endogenous_field rule classical p positive belowOne fixedPoint
      constant growth constantPositive growthPositive meanBounds value valueFixed valuePositive
      lower upper lowerPositive upperPositive comparison order orderFinite
  refine ⟨constant, growth, constantPositive, constantAtMostOne, growthLower, growthUpper, meanBounds, ?_, ?_⟩
  · intro order orderAtLeastOne orderFinite
    letI : Fact (1 ≤ order) := ⟨orderAtLeastOne⟩
    have supremum := supremumProperties order orderFinite
    have envelope := chemicalTerminalEnvelope_moments_and_bound_of_orbit_supremum rule classical p positive belowOne fixedPoint
      growth growthPositive order supremum.1 supremum.2
    exact ⟨_, supremum.1.eLpNorm_lt_top.ne, fun address opened => ⟨envelope.1 address opened, envelope.2.1 address opened⟩⟩
  · have supremum := supremumProperties 2 (by norm_num)
    exact (chemicalTerminalEnvelope_moments_and_bound_of_orbit_supremum rule classical p positive belowOne fixedPoint
      growth growthPositive 2 supremum.1 supremum.2).2.2

end IGSIII.Chemical.Substitution
