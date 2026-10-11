import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! Kolmogorov existence for compact countable products, obtained directly
from compactness of probability measures. Consistent finite-history laws
are extended by a fixed point; every weak subsequential limit has exactly
the prescribed finite marginals. -/
set_option autoImplicit false
set_option maxHeartbeats 2800000
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory Filter Preorder
open scoped Topology

variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]
  [MeasurableSpace Space] [BorelSpace Space]

def compactPrefixExtensionCompletion20261011 (point : Space) (depth : ℕ)
    (history : Finset.Iic depth → Space) : ℕ → Space :=
  fun index => if below : index ≤ depth then history ⟨index, Finset.mem_Iic.mpr below⟩ else point

theorem compactPrefixExtension_continuous_completion20261011
    (point : Space) (depth : ℕ) :
    Continuous (compactPrefixExtensionCompletion20261011 point depth) := by
  apply continuous_pi
  intro index
  by_cases below : index ≤ depth
  · simpa only [compactPrefixExtensionCompletion20261011, dif_pos below] using
      (continuous_apply (⟨index, Finset.mem_Iic.mpr below⟩ : Finset.Iic depth) : Continuous (fun history : Finset.Iic depth → Space => history ⟨index, Finset.mem_Iic.mpr below⟩))
  · simp only [compactPrefixExtensionCompletion20261011, dif_neg below]
    exact continuous_const

theorem compact_projective_prefix_exists_completion20261011
    (point : Space)
    (prefixLaw : (depth : ℕ) → ProbabilityMeasure (Finset.Iic depth → Space))
    (compatible : ∀ first second : ℕ, ∀ below : first ≤ second,
      (prefixLaw second : Measure (Finset.Iic second → Space)).map (frestrictLe₂ (π := fun _ => Space) below) =
        (prefixLaw first : Measure (Finset.Iic first → Space))) :
    ∃ law : ProbabilityMeasure (ℕ → Space), ∀ depth : ℕ,
      (law : Measure (ℕ → Space)).map (frestrictLe depth) =
        (prefixLaw depth : Measure (Finset.Iic depth → Space)) := by
  let laws : ℕ → ProbabilityMeasure (ℕ → Space) := fun depth =>
    (prefixLaw depth).map
      (compactPrefixExtension_continuous_completion20261011 point depth).measurable.aemeasurable
  obtain ⟨law, _, selected, selectedStrict, convergence⟩ :=
    (isCompact_univ (X := ProbabilityMeasure (ℕ → Space))).tendsto_subseq
      (x := laws) (fun _ => Set.mem_univ _)
  refine ⟨law, fun depth => ?_⟩
  have finiteConvergence := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun index => laws (selected index)) law convergence
    (show Continuous (frestrictLe depth : (ℕ → Space) → (Finset.Iic depth → Space)) from by
      apply continuous_pi
      intro index
      exact continuous_apply index.val)
  have eventuallySame : ∀ᶠ index in atTop,
      (laws (selected index)).map (measurable_frestrictLe depth).aemeasurable = prefixLaw depth := by
    filter_upwards [selectedStrict.tendsto_atTop.eventually_ge_atTop depth] with index below
    apply Subtype.ext
    change (((prefixLaw (selected index) : Measure (Finset.Iic (selected index) → Space)).map
      (compactPrefixExtensionCompletion20261011 point (selected index))).map (frestrictLe depth)) = _
    rw [Measure.map_map (measurable_frestrictLe depth)
      (compactPrefixExtension_continuous_completion20261011 point (selected index)).measurable]
    have mapsSame : (frestrictLe depth) ∘ compactPrefixExtensionCompletion20261011 point (selected index) = frestrictLe₂ (π := fun _ => Space) below := by
      funext history index
      simp only [Function.comp_apply, frestrictLe_apply,
        compactPrefixExtensionCompletion20261011, dif_pos (le_trans (Finset.mem_Iic.mp index.property) below)]
      rfl
    rw [mapsSame, compatible depth (selected index) below]
    rfl
  have eventuallyEq : (fun index => (laws (selected index)).map (measurable_frestrictLe depth).aemeasurable) =ᶠ[atTop] (fun _ => prefixLaw depth) := eventuallySame
  have unique := tendsto_nhds_unique finiteConvergence
    (tendsto_const_nhds.congr' eventuallyEq.symm)
  exact congrArg (fun probability : ProbabilityMeasure (Finset.Iic depth → Space) =>
    (probability : Measure (Finset.Iic depth → Space))) unique

end
end IGSIII34.Spectral
