import IGSIII34.Spectral.Collars.ActualAnnealedStartingConvergence
import IGSIII34.ResistanceLimit.RawElectricalMarkedGHP

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry IGSIII.Chemical.Substitution
open IGSIII34.ResistanceLimit IGSIII34.Percolation MeasureTheory Filter
open scoped _root_.Topology

def actualAnnealedPlantedInitial (rule : Rule) (side : Bool) (depth : ℕ)
    (_marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges) :
    Fin (rule.generation depth).vertices :=
  plantedVertex (rule.generation depth).network side

theorem actualAnnealedPlantedInitial_measurable (rule : Rule) (side : Bool) (depth : ℕ) :
    Measurable (actualAnnealedPlantedInitial rule side depth) := measurable_const

theorem actualAnnealedPlantedInitial_starting_convergence
    (rule : Rule) (p : ℝ) (positive : 0 < p) (belowOne : p < 1)
    (fixedPoint : rule.network.reliability p = p)
    (natural : NaturalResistanceCompletion rule p positive belowOne fixedPoint)
    (side : Bool) :
    ActualAnnealedStartingConvergence rule p positive belowOne fixedPoint natural
      (actualAnnealedPlantedInitial rule side) := by
  classical
  apply Eventually.of_forall
  intro marks typical
  refine ⟨actualElectricalTerminal rule p positive belowOne fixedPoint natural.growth
    (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ side, ?_⟩
  have identity (depth : ℕ) :
      actualAnnealedSelectedVertex rule marks depth (actualAnnealedPlantedInitial rule side depth marks) =
      rawElectricalTerminal rule p positive belowOne fixedPoint natural.growth
        (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth side := by
    have retained := (rawElectricalTerminal rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth side).property
    change ((rule.generation depth).network.openGraph (stationaryConfiguration rule marks depth)).Reachable
      (rule.generation depth).network.source (plantedVertex (rule.generation depth).network side) at retained
    apply Subtype.ext
    simp only [actualAnnealedSelectedVertex, actualAnnealedPlantedInitial, dif_pos retained]
    rfl
  have bornIdentity (depth : ℕ) := actual_electrical_terminal_birth_identity rule p positive belowOne fixedPoint
    natural.growth (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ depth side
  simpa only [identity, bornIdentity] using (tendsto_const_nhds :
    Tendsto (fun _depth : ℕ => actualElectricalTerminal rule p positive belowOne fixedPoint natural.growth
      (natural.amplitude • natural.field) (zero_lt_one.trans natural.aboveOne) ⟨marks, typical.1.1⟩ side) atTop (𝓝 _))

end
end IGSIII34.Spectral
