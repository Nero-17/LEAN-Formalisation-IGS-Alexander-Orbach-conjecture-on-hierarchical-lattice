import IGSIII34.Spectral.ActualPrefixHarmonicCompletion
import IGSIII34.Spectral.NestedPathBlockCompletion
import IGSIII34.Spectral.ActualLocalEvaluationCompletion
import IGSIII34.ResistanceLimit.ElectricalBoundaryCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Probability IGSIII34.Percolation IGSIII34.ResistanceLimit IGSIII34.Forms Resistance
open MeasureTheory Filter
open scoped BigOperators _root_.Topology

variable (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
  (fixedPoint : rule.network.reliability p = p) (growth : ℝ)
  (value : Lp ℝ 2 (independentInnovationLaw rule p positive belowOne fixedPoint))
  (growthPositive : 0 < growth)
  (marks : {marks // StationaryHarmonicTypical rule p positive belowOne fixedPoint growth value marks})

def actualHarmonicCompletionFunctionCompletion
    (initial : ℕ) (boundary : Fin (rule.generation initial).vertices → ℝ) :
    C(UniformSpace.Completion (ActualStationaryEnergySkeleton rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)), ℝ) :=
  actualEnergyExtensionLinear rule p positive belowOne fixedPoint growth value growthPositive
    (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks)
    ⟨actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks initial boundary,
      actualHarmonicFunction_finite rule p positive belowOne fixedPoint growth value growthPositive marks initial boundary⟩

theorem actual_harmonic_completion_prefix_anchor_value_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (coarse fine : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (parentWord : Fin (coarse + 1) → (Fin rule.edges × Bool))
    (suffix : Fin (fine + 1) → (Fin rule.edges × Bool))
    (parentLive : retainedComponentState rule marks.val (List.ofFn parentWord) ≠ .inactive)
    (live : retainedComponentState rule marks.val
      (List.ofFn (blockWordAppendCompletion coarse fine parentWord suffix)) ≠ .inactive)
    (flatAvailable : stationaryConfiguration rule marks.val coarse
      (generationWordEdge rule coarse (fun index => (parentWord index).1)) = true →
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint
          (generationWordEdge rule coarse (fun index => (parentWord index).1))).1 =
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint
          (generationWordEdge rule coarse (fun index => (parentWord index).1))).2) :
    actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
      (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property.1.1
        (coarse + fine + 1) (blockWordAppendCompletion coarse fine parentWord suffix)) =
      boundary (componentWordAnchor rule marks.val coarse parentWord) := by
  rw [actualElectricalComponentWordPoint, dif_pos live]
  refine (completionExtension_coe
    (actualEnergyEndpoint rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance rule p positive belowOne fixedPoint growth value
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actualEnergyConductance_nonnegative rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    (actual_finite_energy_resistance_bound rule p positive belowOne fixedPoint growth value growthPositive
      (harmonicTypicalEnergyMarks rule p positive belowOne fixedPoint growth value marks))
    ⟨actualHarmonicFunction rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary,
      actualHarmonicFunction_finite rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary⟩
    (electricalSkeletonVertex rule (stationaryConfiguration rule marks.val)
      (typicalStationaryCoherent rule p positive belowOne fixedPoint growth value ⟨marks.val, marks.property.1.1⟩)
      (stationaryResistance rule p positive belowOne fixedPoint growth value marks.val)
      (typicalStationaryResistance_positive rule p positive belowOne fixedPoint growth value growthPositive
        ⟨marks.val, marks.property.1.1⟩) marks.property.1.1.2.2 (coarse + fine + 1)
      ⟨componentWordAnchor rule marks.val (coarse + fine + 1) (blockWordAppendCompletion coarse fine parentWord suffix),
        componentWordAnchor_retained rule marks.val marks.property.1.1.2.1 _ _ live⟩)).trans ?_
  exact actual_component_prefix_harmonic_anchor_completion rule p positive belowOne fixedPoint growth value growthPositive marks
    stationary coarse fine boundary parentWord suffix parentLive live flatAvailable

/-- The actual harmonic function has the prescribed constant value on the
realization of a cylinder whose available roots carry that value. The proof
uses genuine descendant anchors and their established geometric convergence. -/
theorem actual_harmonic_boundary_realization_prefix_value_completion
    (stationary : ∀ address, electricalCell rule.network (marks.val (address, true))
      (fun edge => electricalField rule p positive belowOne fixedPoint value (address ++ [edge]) marks.val) =
        growth * electricalField rule p positive belowOne fixedPoint value address marks.val)
    (boundaryLaw : Measure (Π depth, Fin depth → (Fin rule.edges × Bool)))
    (retainedPaths : ∀ᵐ path ∂boundaryLaw, ∀ depth,
      Fin.init (path (depth + 1)) = path depth ∧ retainedComponentState rule marks.val (List.ofFn (path depth)) ≠ .inactive)
    (realization : (Π depth, Fin depth → (Fin rule.edges × Bool)) →
      ActualStationaryElectricalSpace rule p positive belowOne fixedPoint growth value growthPositive ⟨marks.val, marks.property.1.1⟩)
    (convergence : ∀ᵐ path ∂boundaryLaw, Tendsto (fun depth =>
      actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property.1.1
        depth (path (depth + 1))) atTop (𝓝 (realization path)))
    (coarse : ℕ) (boundary : Fin (rule.generation coarse).vertices → ℝ)
    (parentWord : Fin (coarse + 1) → (Fin rule.edges × Bool))
    (flatAvailable : stationaryConfiguration rule marks.val coarse
      (generationWordEdge rule coarse (fun index => (parentWord index).1)) = true →
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint
          (generationWordEdge rule coarse (fun index => (parentWord index).1))).1 =
      sourceProjection (network (rule.generation coarse).network (stationaryConfiguration rule marks.val coarse)) boundary
        ((rule.generation coarse).network.endpoint
          (generationWordEdge rule coarse (fun index => (parentWord index).1))).2) :
    ∀ᵐ path ∂boundaryLaw, path (coarse + 1) = parentWord →
      actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
        (realization path) = boundary (componentWordAnchor rule marks.val coarse parentWord) := by
  filter_upwards [retainedPaths, convergence] with path retained converges
  intro parentIdentity
  have values (fine : ℕ) :
      actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive marks coarse boundary
        (actualElectricalComponentWordPoint rule p positive belowOne fixedPoint growth value growthPositive marks.val marks.property.1.1
          (coarse + fine + 1) (path (coarse + fine + 2))) =
        boundary (componentWordAnchor rule marks.val coarse parentWord) := by
    obtain ⟨suffix, decomposition⟩ := nested_path_block_decomposition_completion path
      (fun depth => (retained depth).1) coarse fine
    rw [parentIdentity] at decomposition
    rw [decomposition]
    exact actual_harmonic_completion_prefix_anchor_value_completion rule p positive belowOne fixedPoint growth value growthPositive
      marks stationary coarse fine boundary parentWord suffix (by rw [← parentIdentity]; exact (retained _).2)
      (by rw [← decomposition]; exact (retained _).2) flatAvailable
  have subAtTop : Tendsto (fun fine : ℕ => coarse + fine + 1) atTop atTop := by
    convert tendsto_add_atTop_nat (coarse + 1) using 1
    funext fine
    omega
  have limit := (actualHarmonicCompletionFunctionCompletion rule p positive belowOne fixedPoint growth value growthPositive
    marks coarse boundary).continuous.tendsto (realization path) |>.comp (converges.comp subAtTop)
  have constantLimit := (tendsto_const_nhds : Tendsto (fun _fine : ℕ => boundary (componentWordAnchor rule marks.val coarse parentWord))
    atTop (𝓝 (boundary (componentWordAnchor rule marks.val coarse parentWord))))
  have sameLimit := constantLimit.congr' (Eventually.of_forall (fun fine => (values fine).symm))
  exact tendsto_nhds_unique limit sameLimit

end
end IGSIII34.Spectral

