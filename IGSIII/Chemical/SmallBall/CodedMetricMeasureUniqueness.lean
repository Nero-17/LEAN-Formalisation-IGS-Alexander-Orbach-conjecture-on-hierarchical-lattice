import IGSIII.Geometry.ExceptionalTransport
import Mathlib.Topology.MetricSpace.Completion

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace IGSIII.Geometry
noncomputable section

open MeasureTheory Filter UniformSpace
open scoped Topology

/-- The distances between a common dense family determine its complete
metric realization, including repeated labels. -/
theorem exists_isometryEquiv_of_dense_labels
    {Label First Last : Type*} [MetricSpace First] [MetricSpace Last]
    [CompleteSpace First] [CompleteSpace Last]
    (first : Label → First) (last : Label → Last)
    (firstDense : DenseRange first) (lastDense : DenseRange last)
    (distances : ∀ left right, dist (first left) (first right) = dist (last left) (last right)) :
    ∃ equivalence : First ≃ᵢ Last, ∀ label, equivalence (first label) = last label := by
  letI : PseudoMetricSpace Label := PseudoMetricSpace.induced first inferInstance
  have firstIsometry : Isometry first := PseudoMetricSpace.isometry_induced first
  have lastIsometry : Isometry last := Isometry.of_dist_eq (fun left right => (distances left right).symm)
  have firstExtension := firstIsometry.completion_extension
  have lastExtension := lastIsometry.completion_extension
  have firstExtensionDense : DenseRange (Completion.extension first) := firstDense.mono (by
    rintro _ ⟨label, rfl⟩
    exact ⟨(label : Completion Label), Completion.extension_coe firstIsometry.uniformContinuous label⟩)
  have lastExtensionDense : DenseRange (Completion.extension last) := lastDense.mono (by
    rintro _ ⟨label, rfl⟩
    exact ⟨(label : Completion Label), Completion.extension_coe lastIsometry.uniformContinuous label⟩)
  have firstSurjective : Function.Surjective (Completion.extension first) := by
    intro point
    have membership : point ∈ closure (Set.range (Completion.extension first)) := firstExtensionDense point
    rw [firstExtension.isClosedEmbedding.isClosed_range.closure_eq] at membership
    exact membership
  have lastSurjective : Function.Surjective (Completion.extension last) := by
    intro point
    have membership : point ∈ closure (Set.range (Completion.extension last)) := lastExtensionDense point
    rw [lastExtension.isClosedEmbedding.isClosed_range.closure_eq] at membership
    exact membership
  let firstEquivalence : Completion Label ≃ᵢ First :=
    { Equiv.ofBijective (Completion.extension first) ⟨firstExtension.injective, firstSurjective⟩ with
      isometry_toFun := firstExtension }
  let lastEquivalence : Completion Label ≃ᵢ Last :=
    { Equiv.ofBijective (Completion.extension last) ⟨lastExtension.injective, lastSurjective⟩ with
      isometry_toFun := lastExtension }
  refine ⟨firstEquivalence.symm.trans lastEquivalence, ?_⟩
  intro label
  have firstIdentity : firstEquivalence (label : Completion Label) = first label :=
    Completion.extension_coe firstIsometry.uniformContinuous label
  have lastIdentity : lastEquivalence (label : Completion Label) = last label :=
    Completion.extension_coe lastIsometry.uniformContinuous label
  rw [← firstIdentity]
  simpa only [IsometryEquiv.trans_apply, IsometryEquiv.symm_apply_apply] using lastIdentity

/-- Equal labelled atomic approximations determine the limiting probability
measure under the unique dense-label metric identification. -/
theorem isometryEquiv_map_measure_eq_of_atomic_approximations
    {First Last : Type*} [MetricSpace First] [MetricSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    (equivalence : First ≃ᵢ Last) (firstMeasure : Measure First) (lastMeasure : Measure Last)
    [IsProbabilityMeasure firstMeasure] [IsProbabilityMeasure lastMeasure]
    (firstAtomic : ℕ → Measure First) (lastAtomic : ℕ → Measure Last)
    (atomicIdentity : ∀ depth, (firstAtomic depth).map equivalence = lastAtomic depth)
    (firstConvergence : Tendsto (fun depth => levyProkhorovEDist (firstAtomic depth) firstMeasure) atTop (𝓝 0))
    (lastConvergence : Tendsto (fun depth => levyProkhorovEDist (lastAtomic depth) lastMeasure) atTop (𝓝 0)) :
    firstMeasure.map equivalence = lastMeasure := by
  have upper : ∀ depth, levyProkhorovEDist (firstMeasure.map equivalence) lastMeasure ≤
      levyProkhorovEDist (firstAtomic depth) firstMeasure + levyProkhorovEDist (lastAtomic depth) lastMeasure := by
    intro depth
    have transported := levyProkhorovEDist_map_le_of_lipschitz_one firstMeasure (firstAtomic depth)
      equivalence equivalence.isometry.lipschitz
    rw [atomicIdentity depth, levyProkhorovEDist_comm firstMeasure] at transported
    exact (levyProkhorovEDist_triangle _ _ _).trans (add_le_add transported le_rfl)
  have zeroDistance : levyProkhorovEDist (firstMeasure.map equivalence) lastMeasure = 0 := by
    apply le_antisymm _ bot_le
    have convergence := firstConvergence.add lastConvergence
    simp only [add_zero] at convergence
    exact ge_of_tendsto convergence (Eventually.of_forall upper)
  letI : IsProbabilityMeasure (firstMeasure.map equivalence) :=
    Measure.isProbabilityMeasure_map equivalence.continuous.measurable.aemeasurable
  apply ext_of_generate_finite (μ := firstMeasure.map equivalence) (ν := lastMeasure)
    {event | IsClosed event} ?_ isPiSystem_isClosed _ (by simp)
  · rw [BorelSpace.measurable_eq (α := Last), borel_eq_generateFrom_isClosed]
  · intro event closed
    exact measure_eq_measure_of_levyProkhorovEDist_eq_zero_of_isClosed zeroDistance closed
      ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩ ⟨1, Real.zero_lt_one, measure_ne_top _ _⟩

/-- A faithful coded realization is unique as a marked metric-measure space.
Its probability measure is specified by the genuine atomic projections, not
by measurability of a boundary realization within a fixed sample. -/
theorem exists_marked_measure_isometryEquiv_of_dense_labels
    {Label First Last : Type*} [MetricSpace First] [MetricSpace Last]
    [CompleteSpace First] [CompleteSpace Last]
    [MeasurableSpace First] [MeasurableSpace Last] [BorelSpace First] [BorelSpace Last]
    (first : Label → First) (last : Label → Last)
    (firstDense : DenseRange first) (lastDense : DenseRange last)
    (distances : ∀ left right, dist (first left) (first right) = dist (last left) (last right))
    (firstMeasure : Measure First) (lastMeasure : Measure Last)
    [IsProbabilityMeasure firstMeasure] [IsProbabilityMeasure lastMeasure]
    (firstAtomic : ℕ → Measure First) (lastAtomic : ℕ → Measure Last)
    (atomicIdentity : ∀ equivalence : First ≃ᵢ Last, (∀ label, equivalence (first label) = last label) →
      ∀ depth, (firstAtomic depth).map equivalence = lastAtomic depth)
    (firstConvergence : Tendsto (fun depth => levyProkhorovEDist (firstAtomic depth) firstMeasure) atTop (𝓝 0))
    (lastConvergence : Tendsto (fun depth => levyProkhorovEDist (lastAtomic depth) lastMeasure) atTop (𝓝 0))
    (mark : Bool → Label) :
    ∃ equivalence : First ≃ᵢ Last,
      (∀ label, equivalence (first label) = last label) ∧
      firstMeasure.map equivalence = lastMeasure ∧
      ∀ side, equivalence (first (mark side)) = last (mark side) := by
  obtain ⟨equivalence, labels⟩ := exists_isometryEquiv_of_dense_labels first last firstDense lastDense distances
  exact ⟨equivalence, labels, isometryEquiv_map_measure_eq_of_atomic_approximations equivalence
    firstMeasure lastMeasure firstAtomic lastAtomic (atomicIdentity equivalence labels) firstConvergence lastConvergence,
    fun side => labels (mark side)⟩

end
end IGSIII.Geometry
