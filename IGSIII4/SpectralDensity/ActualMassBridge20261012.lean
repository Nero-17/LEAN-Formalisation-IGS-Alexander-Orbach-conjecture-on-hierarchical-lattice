import IGSIII4.SpectralDensity.ActualCrossing20261012
import IGSIII4.SpectralDensity.ActualMassLower20261012

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork

def LongEvent (blocks paths interior : ℕ)
    (configuration : Configuration (Fintype.card (Edge blocks paths interior))) : Prop :=
  configuration (Fintype.equivFin _ (.inl 2)) = true ∧
    configuration (Fintype.equivFin _ (.inl 3)) = true ∧
      ChainCrosses blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge))

def selectedFirstEdges (blocks paths interior : ℕ) :
    Finset (Fin (Fintype.card (Edge blocks paths interior))) :=
  Finset.univ.image (firstEdgeIndex blocks paths interior)

theorem selectedFirstEdges_card (blocks paths interior : ℕ) :
    (selectedFirstEdges blocks paths interior).card = blocks * paths := by
  rw [selectedFirstEdges, Finset.card_image_of_injective _ (firstEdgeIndex_injective blocks paths interior)]
  simp

theorem longEvent_subcrossing (blocks paths interior : ℕ)
    (configuration : Configuration (Fintype.card (Edge blocks paths interior)))
    (event : LongEvent blocks paths interior configuration) :
    (network blocks paths interior).crosses configuration = true := by
  apply (network_crosses_iff_circuit configuration).mpr
  exact Or.inr event

theorem longEvent_mono (blocks paths interior : ℕ)
    {first second : Configuration (Fintype.card (Edge blocks paths interior))}
    (inclusion : ∀ edge, first edge = true → second edge = true)
    (event : LongEvent blocks paths interior first) : LongEvent blocks paths interior second := by
  refine ⟨inclusion _ event.1, inclusion _ event.2.1, ?_⟩
  intro block
  obtain ⟨path, opened⟩ := event.2.2 block
  exact ⟨path, fun edge => inclusion _ (opened edge)⟩

theorem longEvent_increasing (blocks paths interior : ℕ)
    (edge : Fin (Fintype.card (Edge blocks paths interior))) (rest : RemainingConfiguration edge)
    (event : LongEvent blocks paths interior (insertEdge edge false rest)) :
    LongEvent blocks paths interior (insertEdge edge true rest) := by
  apply longEvent_mono blocks paths interior (event := event)
  intro other opened
  by_cases equal : other = edge
  · subst other; simp [insertEdge_self]
  · simpa only [insertEdge_other edge false rest other equal,
      insertEdge_other edge true rest other equal] using opened

theorem longEvent_first_edge_retained (blocks paths interior : ℕ)
    (configuration : Configuration (Fintype.card (Edge blocks paths interior)))
    (event : LongEvent blocks paths interior configuration)
    (edge : Fin (Fintype.card (Edge blocks paths interior)))
    (member : edge ∈ selectedFirstEdges blocks paths interior) (opened : configuration edge = true) :
    (network blocks paths interior).childState .connected configuration edge = some .connected := by
  obtain ⟨pair, _, rfl⟩ := Finset.mem_image.mp member
  have retained := long_crossing_first_edge_retained blocks paths interior
    (fun edge => configuration (Fintype.equivFin _ edge)) event.1 event.2.2 pair.1 pair.2 opened
  simpa only [Equiv.apply_symm_apply, firstEdgeIndex] using retained

theorem actual_connected_mass_first_edges_lower (blocks paths interior : ℕ) (probability : ℝ)
    (positive : 0 < probability) (belowOne : probability < 1)
    (critical : (network blocks paths interior).reliability probability = probability) :
    ((blocks * paths : ℕ) : ℝ) *
      expectation probability (fun configuration => if LongEvent blocks paths interior configuration then 1 else 0) ≤
    (network blocks paths interior).massMatrix probability .connected .connected := by
  have lower := connected_mass_lower_of_increasing_subcrossing (network blocks paths interior)
    probability positive belowOne critical (selectedFirstEdges blocks paths interior)
      (LongEvent blocks paths interior) (longEvent_subcrossing blocks paths interior)
      (fun edge _ rest => longEvent_increasing blocks paths interior edge rest)
      (longEvent_first_edge_retained blocks paths interior)
  rwa [selectedFirstEdges_card] at lower

end
end IGSIII4.SpectralDensity.ActualFamily

