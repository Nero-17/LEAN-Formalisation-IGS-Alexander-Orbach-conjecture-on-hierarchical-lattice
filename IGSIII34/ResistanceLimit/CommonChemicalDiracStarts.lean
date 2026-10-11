import IGSIII34.ResistanceLimit.CommonChemicalStartingPoints

set_option autoImplicit false
set_option maxHeartbeats 1400000
namespace IGSIII34.ResistanceLimit
noncomputable section
open Filter MeasureTheory
open scoped _root_.Topology

/-- Every finite starting-vertex sequence converging in the constructed
common chemical realization satisfies the electrical Dirac initial-law
condition of the actual process theorem. -/
theorem common_chemical_dirac_starting_laws_tendsto
    {Vertices : ℕ → Type*} [∀ depth, MeasurableSpace (Vertices depth)]
    {Chemical Electrical Ambient : Type*}
    [MetricSpace Chemical] [MetricSpace Electrical] [MetricSpace Ambient]
    [MeasurableSpace Electrical] [BorelSpace Electrical]
    (homeomorph : Chemical ≃ₜ Electrical)
    (target : Chemical → Ambient) (targetIsometry : Isometry target)
    (chemicalProjections : ∀ depth, Vertices depth → Chemical)
    (electricalProjections : ∀ depth, Vertices depth → Electrical)
    (measurable : ∀ depth, Measurable (electricalProjections depth))
    (birthIdentity : ∀ depth vertex, homeomorph.symm (electricalProjections depth vertex) = chemicalProjections depth vertex)
    (sources : ∀ depth, Vertices depth → Ambient)
    (placementClose : ∀ tolerance : ℝ, 0 < tolerance → ∀ᶠ depth in atTop, ∀ vertex,
      dist (sources depth vertex) (target (chemicalProjections depth vertex)) < tolerance)
    (vertices : ∀ depth, Vertices depth) (point : Chemical)
    (convergence : Tendsto (fun depth => sources depth (vertices depth)) atTop (𝓝 (target point))) :
    Tendsto (fun depth => (diracProba (vertices depth)).map (measurable depth).aemeasurable)
      atTop (𝓝 (diracProba (homeomorph point))) := by
  exact finite_dirac_initial_tendsto electricalProjections measurable vertices (homeomorph point)
    (common_homeomorph_starting_tendsto homeomorph target targetIsometry chemicalProjections electricalProjections
      birthIdentity sources placementClose vertices point convergence)

end
end IGSIII34.ResistanceLimit
