import IGSIII34.ResistanceLimit.ActualCommonChemicalHausdorff
import IGSIII.Chemical.SmallBall.ActualChemicalTerminals
import IGSIII34.Spectral.Collars.CarrierPlacedMass

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Chemical.Substitution IGSIII.Geometry
open IGSIII.Chemical.SmallBall IGSIII34.Spectral MeasureTheory Filter TopologicalSpace
open scoped _root_.Topology

/-- Literal compact image, both ordered marks, and both probability masses
in one prescribed metric ambient. The ambient metric is never recoded. -/
abbrev PlacedMeasuredMarkedState (Ambient : Type*) [MetricSpace Ambient]
    [MeasurableSpace Ambient] :=
  NonemptyCompacts Ambient × (Bool → Ambient) × (Bool → ProbabilityMeasure Ambient)

theorem placed_measured_marked_state_tendsto
    {Ambient : Type*} [MetricSpace Ambient] [MeasurableSpace Ambient] [BorelSpace Ambient]
    (images : ℕ → NonemptyCompacts Ambient) (image : NonemptyCompacts Ambient)
    (marks : ℕ → Bool → Ambient) (mark : Bool → Ambient)
    (masses : ℕ → Bool → ProbabilityMeasure Ambient) (mass : Bool → ProbabilityMeasure Ambient)
    (imagesConverge : Tendsto images atTop (𝓝 image))
    (marksConverge : ∀ side, Tendsto (fun depth => marks depth side) atTop (𝓝 (mark side)))
    (massesConverge : ∀ counting, Tendsto (fun depth => masses depth counting) atTop (𝓝 (mass counting))) :
    Tendsto (fun depth => ((images depth, marks depth, masses depth) : PlacedMeasuredMarkedState Ambient))
      atTop (𝓝 (image, mark, mass)) := by
  simpa only [nhds_prod_eq] using
    imagesConverge.prodMk ((tendsto_pi_nhds.mpr marksConverge).prodMk
      (tendsto_pi_nhds.mpr massesConverge))

variable (rule : Rule) (classicalRule : rule.Classical)
  (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
  (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
  (coherent : configurationSequenceCoherent rule (fun depth => markedGenerationConfiguration rule marks depth [] true))
  (scale : ℝ) (scalePositive : 0 < scale)
  (lengths : ∀ depth, Fin (rule.generation depth).edges → ℝ)
  (nonnegative : ∀ depth edge, 0 ≤ lengths depth edge)
  (positive : ∀ depth edge, markedGenerationConfiguration rule marks depth [] true edge = true → 0 < lengths depth edge)
  (childConvergence : ∀ coarse edge, Tendsto (fun fine =>
    (((rule.generation fine).network.openGraph (generationBlockCells rule coarse fine
      (markedGenerationConfiguration rule marks (coarse + fine + 1) [] true) edge)).dist
      (rule.generation fine).network.source (rule.generation fine).network.target : ℝ) /
      scale ^ (coarse + fine + 2)) atTop (𝓝 (lengths coarse edge)))

variable {Ambient : Type*} [MetricSpace Ambient]
  (target : ActualChemicalSpace rule classicalRule (fun depth => markedGenerationConfiguration rule marks depth [] true)
    coherent scale scalePositive lengths nonnegative positive childConvergence → Ambient)
  (targetIsometry : Isometry target)
  (sources : ∀ depth, ActualFiniteCluster rule (fun depth => markedGenerationConfiguration rule marks depth [] true) scale scalePositive depth → Ambient)
  (sourceIsometry : ∀ depth, Isometry (sources depth))
  (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
    dist (sources depth vertex) (target (actualChemicalVertex rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence depth vertex)) < tolerance)

include placementClose in
/-- Both ordered original terminals converge under the very same source
isometries. No new ambient or terminal placement is selected. -/
theorem actual_common_chemical_terminal_tendsto (side : Bool) :
    Tendsto (fun depth => sources depth (actualFiniteClusterTerminal rule
      (fun depth => markedGenerationConfiguration rule marks depth [] true)
      (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true)
      scale scalePositive depth side)) atTop
      (𝓝 (target (actualChemicalTerminal rule classicalRule
        (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true)
        scale scalePositive lengths nonnegative positive childConvergence side))) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance tolerancePositive
  filter_upwards [placementClose tolerance tolerancePositive] with depth near
  rw [actualChemicalTerminal_eq_vertex rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
    (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true)
    scale scalePositive lengths nonnegative positive childConvergence depth side]
  exact near _

include placementClose in
theorem actual_common_chemical_measured_marked_state_tendsto
    [MeasurableSpace Ambient] [BorelSpace Ambient]
    (eta coefficient : ℝ) (start : ℕ) (etaNonnegative : 0 ≤ eta) (etaBelowOne : eta < 1)
    (coefficientNonnegative : 0 ≤ coefficient)
    (radiusBounds : ∀ address opened depth, start ≤ address.length →
      (markedTerminalComponentRadius rule marks depth address opened : ℝ) / scale ^ (depth + 1 + address.length) ≤
        coefficient * eta ^ address.length)
    (masses : ℕ → Bool → ProbabilityMeasure Ambient) (mass : Bool → ProbabilityMeasure Ambient)
    (massesConverge : ∀ counting, Tendsto (fun depth => masses depth counting) atTop (𝓝 (mass counting))) :
    letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
      (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
      marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
    Tendsto (fun depth => ((continuousNonemptyCompactRange (sources depth) (sourceIsometry depth).continuous,
      (fun side => sources depth (actualFiniteClusterTerminal rule
        (fun depth => markedGenerationConfiguration rule marks depth [] true)
        (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true)
        scale scalePositive depth side)), masses depth) : PlacedMeasuredMarkedState Ambient)) atTop
      (𝓝 (continuousNonemptyCompactRange target targetIsometry.continuous,
        (fun side => target (actualChemicalTerminal rule classicalRule
          (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent
          (fun depth => markedGenerationConfiguration_crosses rule marks crossing depth [] true)
          scale scalePositive lengths nonnegative positive childConvergence side)), mass)) := by
  letI := actualChemicalSpace_compact_of_component_radius_bounds rule classicalRule
    (fun depth => markedGenerationConfiguration rule marks depth [] true) coherent scale scalePositive lengths nonnegative positive childConvergence
    marks (fun _ => rfl) eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds
  exact placed_measured_marked_state_tendsto _ _ _ _ masses mass
    (actual_common_chemical_compact_images_tendsto rule classicalRule marks coherent scale scalePositive
      lengths nonnegative positive childConvergence target targetIsometry sources sourceIsometry placementClose
      eta coefficient start etaNonnegative etaBelowOne coefficientNonnegative radiusBounds)
    (fun side => actual_common_chemical_terminal_tendsto rule classicalRule marks crossing coherent scale scalePositive
      lengths nonnegative positive childConvergence target sources placementClose side) massesConverge

end
end IGSIII34.ResistanceLimit
