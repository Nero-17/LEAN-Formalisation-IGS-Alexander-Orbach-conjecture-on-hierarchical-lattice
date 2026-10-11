import IGSIII34.ResistanceLimit.ActualCommonChemicalPaperLaw
import Mathlib.MeasureTheory.Measure.DiracProba

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Filter MeasureTheory
open scoped _root_.Topology

theorem common_isometric_projection_tendsto
    {Vertices : ℕ → Type*} {Carrier Ambient : Type*} [MetricSpace Carrier] [MetricSpace Ambient]
    (target : Carrier → Ambient) (targetIsometry : Isometry target)
    (projections : ∀ depth, Vertices depth → Carrier) (sources : ∀ depth, Vertices depth → Ambient)
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ point,
      dist (sources depth point) (target (projections depth point)) < tolerance)
    (vertices : ∀ depth, Vertices depth) (point : Carrier)
    (convergence : Tendsto (fun depth => sources depth (vertices depth)) atTop (𝓝 (target point))) :
    Tendsto (fun depth => projections depth (vertices depth)) atTop (𝓝 point) := by
  apply Metric.tendsto_nhds.mpr
  intro tolerance positive
  filter_upwards [placementClose (tolerance / 2) (by positivity),
    Metric.tendsto_nhds.mp convergence (tolerance / 2) (by positivity)] with depth close near
  have triangle := dist_triangle (target (projections depth (vertices depth)))
    (sources depth (vertices depth)) (target point)
  rw [targetIsometry.dist_eq, dist_comm (target (projections depth (vertices depth))) (sources depth (vertices depth))] at triangle
  exact triangle.trans_lt (by linarith [close (vertices depth)])

theorem common_homeomorph_starting_tendsto
    {Vertices : ℕ → Type*} {Chemical Electrical Ambient : Type*}
    [MetricSpace Chemical] [MetricSpace Electrical] [MetricSpace Ambient]
    (homeomorph : Chemical ≃ₜ Electrical)
    (target : Chemical → Ambient) (targetIsometry : Isometry target)
    (chemicalProjections : ∀ depth, Vertices depth → Chemical)
    (electricalProjections : ∀ depth, Vertices depth → Electrical)
    (birthIdentity : ∀ depth vertex, homeomorph.symm (electricalProjections depth vertex) = chemicalProjections depth vertex)
    (sources : ∀ depth, Vertices depth → Ambient)
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (sources depth vertex) (target (chemicalProjections depth vertex)) < tolerance)
    (vertices : ∀ depth, Vertices depth) (point : Chemical)
    (convergence : Tendsto (fun depth => sources depth (vertices depth)) atTop (𝓝 (target point))) :
    Tendsto (fun depth => electricalProjections depth (vertices depth)) atTop (𝓝 (homeomorph point)) := by
  have chemical := common_isometric_projection_tendsto target targetIsometry chemicalProjections sources placementClose vertices point convergence
  have mapped := homeomorph.continuous.continuousAt.tendsto.comp chemical
  convert mapped using 1
  funext depth
  dsimp only [Function.comp_def]
  rw [← birthIdentity]
  exact (homeomorph.apply_symm_apply _).symm

theorem finite_dirac_initial_tendsto
    {Vertices : ℕ → Type*} [∀ depth, MeasurableSpace (Vertices depth)]
    {Carrier : Type*} [MetricSpace Carrier] [MeasurableSpace Carrier] [BorelSpace Carrier]
    (projections : ∀ depth, Vertices depth → Carrier) (measurable : ∀ depth, Measurable (projections depth))
    (vertices : ∀ depth, Vertices depth) (point : Carrier)
    (convergence : Tendsto (fun depth => projections depth (vertices depth)) atTop (𝓝 point)) :
    Tendsto (fun depth => (diracProba (vertices depth)).map (measurable depth).aemeasurable)
      atTop (𝓝 (diracProba point)) := by
  have projected (depth : ℕ) : (diracProba (vertices depth)).map (measurable depth).aemeasurable =
      diracProba (projections depth (vertices depth)) := by
    apply ProbabilityMeasure.toMeasure_injective
    exact Measure.map_dirac' (measurable depth) (vertices depth)
  simpa only [projected, Function.comp_def] using continuous_diracProba.continuousAt.tendsto.comp convergence

end
end IGSIII34.ResistanceLimit
