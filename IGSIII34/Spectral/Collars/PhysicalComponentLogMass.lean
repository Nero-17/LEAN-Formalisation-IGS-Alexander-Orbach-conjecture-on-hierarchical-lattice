import IGSIII34.Spectral.Collars.TypicalLogMass
import IGSIII34.Spectral.Collars.PhysicalCellSelection
import Mathlib.MeasureTheory.MeasurableSpace.MeasurablyGenerated

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology

/-- A finite, measurable choice of a genuinely containing closed component.
The fallback is used only where none of the finite cells contains the point. -/
def selectedContainingComponentLabel {Point Index : Type*} [Fintype Index]
    (cell : Index → Set Point) (fallback : Index) (point : Point) : Index := by
  classical
  exact Finset.univ.toList.foldr (fun label selected => if point ∈ cell label then label else selected) fallback

theorem selectedContainingComponentLabel_measurable
    {Point Index : Type*} [MeasurableSpace Point] [MeasurableSpace Index] [Fintype Index]
    (cell : Index → Set Point) (fallback : Index) (cellMeasurable : ∀ label, MeasurableSet (cell label)) :
    Measurable (selectedContainingComponentLabel cell fallback) := by
  classical
  have measurable : ∀ labels : List Index, Measurable (fun point : Point =>
      labels.foldr (fun label selected => if point ∈ cell label then label else selected) fallback) := by
    intro labels
    induction labels with
    | nil => exact measurable_const
    | cons label labels inductionHypothesis =>
      exact measurable_const.ite (cellMeasurable label) inductionHypothesis
  exact measurable _

theorem selectedContainingComponentLabel_eq_of_unique
    {Point Index : Type*} [Fintype Index] (cell : Index → Set Point) (fallback selected : Index)
    (point : Point) (unique : ∀ label, point ∈ cell label ↔ label = selected) :
    selectedContainingComponentLabel cell fallback point = selected := by
  classical
  have formula : ∀ labels : List Index,
      labels.foldr (fun label chosen => if point ∈ cell label then label else chosen) fallback =
        if selected ∈ labels then selected else fallback := by
    intro labels
    induction labels with
    | nil => simp
    | cons label labels inductionHypothesis =>
      by_cases same : label = selected
      · simp [List.foldr_cons, same, (unique selected).mpr rfl]
      · have absent : point ∉ cell label := fun member => same ((unique label).mp member)
        simp [List.foldr_cons, absent, Ne.symm same, inductionHypothesis]
  simpa only [selectedContainingComponentLabel, Finset.mem_toList, Finset.mem_univ, if_true] using formula Finset.univ.toList

/-- Prefix masses and their logarithmic limit become a physical-point
closed-component statement under the same pushforward mass. -/
theorem pushforward_closed_component_log_mass
    {Path Point : Type*} [MeasurableSpace Path] [MeasurableSpace Point]
    {Index : ℕ → Type*} [∀ depth, Fintype (Index depth)]
    [∀ depth, MeasurableSpace (Index depth)] [∀ depth, MeasurableSingletonClass (Index depth)]
    (boundary : Measure Path) (realization : Path → Point) (realizationMeasurable : Measurable realization)
    (cell : ∀ depth, Index depth → Set Point)
    (cellMeasurable : ∀ depth label, MeasurableSet (cell depth label))
    (fallback : ∀ depth, Index depth) (originalPrefix : ∀ depth, Path → Index depth)
    (weight : ∀ depth, Index depth → ℝ) (weightNonnegative : ∀ depth label, 0 ≤ weight depth label)
    (cellMass : ∀ depth label, (boundary.map realization) (cell depth label) = ENNReal.ofReal (weight depth label))
    (prefixIdentification : ∀ depth, ∀ᵐ path ∂boundary, ∀ label,
      realization path ∈ cell depth label ↔ originalPrefix depth path = label)
    (limit : ℝ)
    (logarithm : ∀ᵐ path ∂boundary, Tendsto (fun depth =>
      Real.log (weight depth (originalPrefix depth path)) / (depth + 1 : ℝ)) atTop (𝓝 limit)) :
    (∀ depth, Measurable (selectedContainingComponentLabel (cell depth) (fallback depth))) ∧
    (∀ᵐ point ∂boundary.map realization,
      (∀ depth, point ∈ cell depth (selectedContainingComponentLabel (cell depth) (fallback depth) point)) ∧
      Tendsto (fun depth => Real.log (((boundary.map realization)
        (cell depth (selectedContainingComponentLabel (cell depth) (fallback depth) point))).toReal) /
          (depth + 1 : ℝ)) atTop (𝓝 limit)) := by
  classical
  have measurable : ∀ depth, Measurable (selectedContainingComponentLabel (cell depth) (fallback depth)) :=
    fun depth => selectedContainingComponentLabel_measurable _ _ (cellMeasurable depth)
  refine ⟨measurable, ?_⟩
  have membershipMeasurable : MeasurableSet {point : Point | ∀ depth,
      point ∈ cell depth (selectedContainingComponentLabel (cell depth) (fallback depth) point)} := by
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro depth
    have equal : {point : Point | point ∈ cell depth (selectedContainingComponentLabel (cell depth) (fallback depth) point)} =
        ⋃ label, {point : Point | selectedContainingComponentLabel (cell depth) (fallback depth) point = label} ∩ cell depth label := by
      ext point
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
      constructor
      · intro member
        exact ⟨_, rfl, member⟩
      · rintro ⟨label, same, member⟩
        simpa only [same] using member
    rw [equal]
    exact MeasurableSet.iUnion (fun label => ((measurable depth) (measurableSet_singleton label)).inter (cellMeasurable depth label))
  have logMeasurable : ∀ depth, Measurable (fun point : Point =>
      Real.log (((boundary.map realization) (cell depth (selectedContainingComponentLabel (cell depth) (fallback depth) point))).toReal) /
        (depth + 1 : ℝ)) := by
    intro depth
    exact (((measurable_of_finite (fun label => (boundary.map realization) (cell depth label))).comp
      (measurable depth)).ennreal_toReal.log).div_const _
  apply (ae_map_iff realizationMeasurable.aemeasurable
    (membershipMeasurable.inter (measurableSet_tendsto (𝓝 limit) logMeasurable))).mpr
  filter_upwards [ae_all_iff.mpr prefixIdentification, logarithm] with path identification logarithm
  have selected : ∀ depth, selectedContainingComponentLabel (cell depth) (fallback depth) (realization path) = originalPrefix depth path := by
    intro depth
    apply selectedContainingComponentLabel_eq_of_unique
    intro label
    exact (identification depth label).trans eq_comm
  refine ⟨?_, logarithm.congr' (Eventually.of_forall (fun depth => ?_))⟩
  · intro depth
    rw [selected depth]
    exact (identification depth _).mpr rfl
  · dsimp only
    rw [selected depth, cellMass, ENNReal.toReal_ofReal (weightNonnegative depth _)]

end
end IGSIII34.Spectral
