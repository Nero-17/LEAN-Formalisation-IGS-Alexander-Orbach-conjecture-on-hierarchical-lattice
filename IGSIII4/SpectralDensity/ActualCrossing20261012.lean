import IGSIII4.SpectralDensity.ActualFamily20261012

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

/-- A graph walk cannot cross a cut whose labels agree on every open edge. -/
theorem reachable_cut {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (label : Vertex blocks paths interior → Prop)
    (preserved : ∀ edge, configuration edge = true →
      (label (endpoint blocks paths interior edge).1 ↔ label (endpoint blocks paths interior edge).2))
    {first last : Vertex blocks paths interior}
    (reachable : (graph blocks paths interior configuration).Reachable first last) : label first ↔ label last := by
  obtain ⟨walk⟩ := reachable
  induction walk with
  | nil => rfl
  | @cons first middle last adjacent rest previous =>
    obtain ⟨_, edge, opened, forward | backward⟩ := adjacent
    · exact (show label first ↔ label middle from by simpa only [forward] using preserved edge opened).trans previous
    · exact (show label first ↔ label middle from by simpa only [backward] using (preserved edge opened).symm).trans previous

def LeftCut (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool) :
    Vertex blocks paths interior → Prop
  | .inl vertex => vertex.val = 0 ∨ (vertex.val = 1 ∧ configuration (.inl 0) = true)
  | .inr _ => False

theorem reachable_requires_left_exterior {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool)
    (shortFails : ¬(configuration (.inl 0) = true ∧ configuration (.inl 1) = true))
    (reachable : (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (target blocks paths interior)) :
    configuration (.inl 2) = true := by
  by_contra exteriorFails
  have preserved : ∀ edge, configuration edge = true →
      (LeftCut blocks paths interior configuration (endpoint blocks paths interior edge).1 ↔
        LeftCut blocks paths interior configuration (endpoint blocks paths interior edge).2) := by
    intro edge opened
    rcases edge with edge | ⟨block, path, edge⟩
    · fin_cases edge <;> simp_all [endpoint, LeftCut, source, midpoint, target]
    · simp only [endpoint, pathVertex]
      split_ifs <;> simp [LeftCut]
  have cut := reachable_cut configuration (LeftCut blocks paths interior configuration) preserved reachable
  simpa [LeftCut, source, target] using cut

def BlockCut (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool)
    (failed : Fin blocks) : Vertex blocks paths interior → Prop
  | .inl vertex => vertex.val = 0 ∨ (vertex.val = 1 ∧ configuration (.inl 0) = true)
  | .inr (.inl junction) => junction.val ≤ failed.val
  | .inr (.inr (block, path, position)) =>
      block.val < failed.val ∨ (block = failed ∧ ∀ edge : Fin (interior + 2),
        edge.val ≤ position.val → configuration (.inr (block, path, edge)) = true)

theorem pathPrefix_step {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (block : Fin blocks) (path : Fin paths)
    (edge : Fin (interior + 2)) (opened : configuration (.inr (block, path, edge)) = true) :
    (∀ earlier : Fin (interior + 2), earlier.val < edge.val →
      configuration (.inr (block, path, earlier)) = true) ↔
    (∀ earlier : Fin (interior + 2), earlier.val < edge.val + 1 →
      configuration (.inr (block, path, earlier)) = true) := by
  constructor
  · intro initialOpen earlier before
    by_cases equal : earlier = edge
    · subst earlier; exact opened
    · exact initialOpen earlier (by have := Fin.val_ne_of_ne equal; omega)
  · intro initialOpen earlier before
    exact initialOpen earlier (by omega)

theorem blockCut_pathVertex {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) (failed : Fin blocks)
    (failure : ∀ path : Fin paths, ¬∀ edge : Fin (interior + 2),
      configuration (.inr (failed, path, edge)) = true)
    (block : Fin blocks) (path : Fin paths) (position : Fin (interior + 3)) :
    BlockCut blocks paths interior configuration failed
      (pathVertex blocks paths interior block path position) ↔
    block.val < failed.val ∨ (block = failed ∧ ∀ edge : Fin (interior + 2),
      edge.val < position.val → configuration (.inr (block, path, edge)) = true) := by
  have positionBound := position.isLt
  simp only [pathVertex]
  split_ifs with first last
  · simp only [BlockCut, Fin.val_castSucc, first, Nat.not_lt_zero, false_implies, implies_true,
      and_true]
    constructor
    · intro comparison
      by_cases equal : block = failed
      · exact Or.inr equal
      · exact Or.inl (by have := Fin.val_ne_of_ne equal; omega)
    · rintro (comparison | equal)
      · omega
      · subst block; exact le_rfl
  · simp only [BlockCut, Fin.val_succ, last]
    constructor
    · intro comparison; exact Or.inl (by omega)
    · rintro (comparison | ⟨equal, allOpen⟩)
      · omega
      · subst block
        exact False.elim (failure path (fun edge => allOpen edge edge.isLt))
  · simp only [BlockCut]
    constructor
    · rintro (comparison | ⟨equal, initialOpen⟩)
      · exact Or.inl comparison
      · exact Or.inr ⟨equal, fun edge before => initialOpen edge (by omega)⟩
    · rintro (comparison | ⟨equal, initialOpen⟩)
      · exact Or.inl comparison
      · exact Or.inr ⟨equal, fun edge before => initialOpen edge (by omega)⟩

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def RightCut (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool) :
    Vertex blocks paths interior → Prop
  | .inl vertex => vertex.val = 0 ∨ (vertex.val = 1 ∧ configuration (.inl 1) ≠ true)
  | .inr _ => True

theorem reachable_requires_right_exterior {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool)
    (shortFails : ¬(configuration (.inl 0) = true ∧ configuration (.inl 1) = true))
    (reachable : (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (target blocks paths interior)) :
    configuration (.inl 3) = true := by
  by_contra exteriorFails
  have preserved : ∀ edge, configuration edge = true →
      (RightCut blocks paths interior configuration (endpoint blocks paths interior edge).1 ↔
        RightCut blocks paths interior configuration (endpoint blocks paths interior edge).2) := by
    intro edge opened
    rcases edge with edge | ⟨block, path, edge⟩
    · fin_cases edge <;> simp_all [endpoint, RightCut, source, midpoint, target]
    · simp only [endpoint, pathVertex]
      split_ifs <;> simp [RightCut]
  have cut := reachable_cut configuration (RightCut blocks paths interior configuration) preserved reachable
  simpa [RightCut, source, target] using cut

theorem reachable_requires_chain {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool)
    (shortFails : ¬(configuration (.inl 0) = true ∧ configuration (.inl 1) = true))
    (reachable : (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (target blocks paths interior)) :
    ChainCrosses blocks paths interior configuration := by
  by_contra chainFails
  unfold ChainCrosses at chainFails
  push Not at chainFails
  obtain ⟨failed, failure⟩ := chainFails
  have pathFailure : ∀ path : Fin paths, ¬∀ edge : Fin (interior + 2),
      configuration (.inr (failed, path, edge)) = true := by
    intro path allOpen
    obtain ⟨edge, closed⟩ := failure path
    exact closed (allOpen edge)
  have preserved : ∀ edge, configuration edge = true →
      (BlockCut blocks paths interior configuration failed (endpoint blocks paths interior edge).1 ↔
        BlockCut blocks paths interior configuration failed (endpoint blocks paths interior edge).2) := by
    intro edge opened
    rcases edge with edge | ⟨block, path, edge⟩
    · have failedBound := failed.isLt
      fin_cases edge <;> simp_all [endpoint, BlockCut, source, midpoint, target]
      all_goals omega
    · simp only [endpoint, blockCut_pathVertex configuration failed pathFailure,
        Fin.val_castSucc, Fin.val_succ]
      by_cases same : block = failed
      · subst block
        simpa using pathPrefix_step configuration failed path edge opened
      · simp only [same, false_and, or_false]
  have cut := reachable_cut configuration (BlockCut blocks paths interior configuration failed) preserved reachable
  simpa [BlockCut, source, target] using cut

theorem reachable_iff_circuit {blocks paths interior : ℕ}
    (configuration : Edge blocks paths interior → Bool) :
    (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (target blocks paths interior) ↔
    CircuitCrosses blocks paths interior configuration := by
  constructor
  · intro reachable
    by_cases short : configuration (.inl 0) = true ∧ configuration (.inl 1) = true
    · exact Or.inl short
    · exact Or.inr ⟨reachable_requires_left_exterior configuration short reachable,
        reachable_requires_right_exterior configuration short reachable,
        reachable_requires_chain configuration short reachable⟩
  · exact circuit_crossing_implies_reachable blocks paths interior configuration

theorem network_crosses_iff_circuit {blocks paths interior : ℕ}
    (configuration : Fin (Fintype.card (Edge blocks paths interior)) → Bool) :
    (network blocks paths interior).crosses configuration = true ↔
      CircuitCrosses blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge)) := by
  rw [(network blocks paths interior).crosses_eq_true]
  let typedConfiguration : Edge blocks paths interior → Bool :=
    fun edge => configuration (Fintype.equivFin _ edge)
  have equivalence := @SimpleGraph.Iso.reachable_iff _ _ _ _
    (graphIso blocks paths interior typedConfiguration)
      (source blocks paths interior) (target blocks paths interior)
  change ((network blocks paths interior).openGraph
    (fun edge => typedConfiguration ((Fintype.equivFin _).symm edge))).Reachable
      (network blocks paths interior).source (network blocks paths interior).target ↔
    (graph blocks paths interior typedConfiguration).Reachable
      (source blocks paths interior) (target blocks paths interior) at equivalence
  have configurationEqual :
      (fun edge => typedConfiguration ((Fintype.equivFin _).symm edge)) = configuration := by
    funext edge
    simp [typedConfiguration]
  rw [configurationEqual] at equivalence
  exact equivalence.trans (reachable_iff_circuit typedConfiguration)

end
end IGSIII4.SpectralDensity.ActualFamily
