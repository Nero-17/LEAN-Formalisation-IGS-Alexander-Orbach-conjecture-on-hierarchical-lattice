import Universality.Percolation.FarConnectedPairs

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def distanceWindowPairs (R : FiniteNetwork vertices edges) (lower upper : ℝ) :
    Finset (Fin vertices × Fin vertices) :=
  Finset.univ.filter fun pair => lower ≤ (R.fullGraph.dist pair.1 pair.2 : ℝ) ∧
    (R.fullGraph.dist pair.1 pair.2 : ℝ) ≤ upper

def connectedDistanceWindowPairs (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (lower upper : ℝ) :
    Finset (Fin vertices × Fin vertices) := by
  classical
  exact (R.distanceWindowPairs lower upper).filter fun pair =>
    (R.openGraph configuration).Reachable pair.1 pair.2

def averagedWindowConnectivity (R : FiniteNetwork vertices edges)
    (p lower upper : ℝ) : ℝ :=
  (∑ configuration : Configuration edges, bernoulliWeight p configuration *
    (R.connectedDistanceWindowPairs configuration lower upper).card) /
      (R.distanceWindowPairs lower upper).card

theorem connectedDistanceWindowPairs_card_le_far (R : FiniteNetwork vertices edges)
    (configuration : Configuration edges) (lower upper : ℝ) (diameter : ℕ)
    (hdiameter : (diameter : ℝ) < lower) :
    (R.connectedDistanceWindowPairs configuration lower upper).card ≤
      (R.farConnectedPairs configuration diameter).card := by
  apply Finset.card_le_card
  intro pair hpair
  obtain ⟨hwindow, hconnected⟩ := Finset.mem_filter.mp hpair
  have hlower := (Finset.mem_filter.mp hwindow).2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_, hconnected⟩
  exact_mod_cast hdiameter.trans_le hlower

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def interiorPairEmbedding (first second : Fin outerEdges) :
    S.InteriorVertex × S.InteriorVertex ↪
      Fin (Fintype.card (R.SubstitutionVertex S)) × Fin (Fintype.card (R.SubstitutionVertex S)) where
  toFun pair := (R.cellEmbedding S first pair.1.val, R.cellEmbedding S second pair.2.val)
  inj' := by
    intro a b heq
    exact Prod.ext (Subtype.ext ((R.cellEmbedding S first).injective (congrArg Prod.fst heq)))
      (Subtype.ext ((R.cellEmbedding S second).injective (congrArg Prod.snd heq)))

theorem distanceWindowPairs_card_ge_two_cells
    (first second : Fin outerEdges) (lower upper : ℝ)
    (hwindow : ∀ u v : S.InteriorVertex,
      lower ≤ ((R.substitute S).fullGraph.dist (R.cellEmbedding S first u.val)
        (R.cellEmbedding S second v.val) : ℝ) ∧
      ((R.substitute S).fullGraph.dist (R.cellEmbedding S first u.val)
        (R.cellEmbedding S second v.val) : ℝ) ≤ upper) :
    Fintype.card S.InteriorVertex ^ 2 ≤ ((R.substitute S).distanceWindowPairs lower upper).card := by
  have hsubset : Finset.univ.map (R.interiorPairEmbedding S first second) ⊆
      (R.substitute S).distanceWindowPairs lower upper := by
    intro pair hpair
    obtain ⟨pair, _, rfl⟩ := Finset.mem_map.mp hpair
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwindow pair.1 pair.2⟩
  simpa only [Finset.card_map, Finset.card_univ, Fintype.card_prod, pow_two] using
    Finset.card_le_card hsubset

theorem all_crossing_cells_join_sources
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (hcrossing : ∀ edge, S.crosses (configuration edge) = true)
    (first second : Fin outerEdges) (u v : Fin innerVertices)
    (hfirst : (S.openGraph (configuration first)).Reachable S.source u)
    (hsecond : (S.openGraph (configuration second)).Reachable S.source v) :
    ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).Reachable
      (R.cellEmbedding S first u) (R.cellEmbedding S second v) := by
  change ((R.substitute S).openGraph (substitutionConfigurationEquiv configuration)).Reachable
    (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S first u))
    (Fintype.equivFin (R.SubstitutionVertex S) (R.cellVertex S second v))
  rw [R.substitute_reachable_iff S]
  have hleft := hfirst.symm.map (R.cellHom S configuration first)
  have hright := hsecond.map (R.cellHom S configuration second)
  change (R.substitutedGraph S configuration).Reachable (R.cellVertex S first u)
    (R.cellVertex S first S.source) at hleft
  change (R.substitutedGraph S configuration).Reachable (R.cellVertex S second S.source)
    (R.cellVertex S second v) at hright
  rw [R.cellVertex_source] at hleft hright
  have hcoarse : S.coarseConfiguration configuration = fun _ => true := funext hcrossing
  have hmiddle := R.coarseReachable_lifts S configuration
    (show (R.openGraph (S.coarseConfiguration configuration)).Reachable
      (R.endpoint first).1 (R.endpoint second).1 from by
        rw [hcoarse]
        exact (houter _).symm.trans (houter _))
  exact hleft.trans (hmiddle.trans hright)

def internalSourceVertices (T : FiniteNetwork vertices edges)
    (configuration : Configuration edges) : Finset T.InteriorVertex :=
  Finset.univ.filter fun vertex => (T.openGraph configuration).reachableDecide T.source vertex.val

theorem internalSourceVertices_card (T : FiniteNetwork vertices edges)
    (configuration : Configuration edges) :
    (T.internalSourceVertices configuration).card = T.internalSelectedMass true false configuration := by
  simp only [internalSourceVertices, Finset.card_eq_sum_ones, Finset.sum_filter,
    internalSelectedMass, selectedActive, Bool.true_and, Bool.false_and, Bool.or_false]

theorem connectedDistanceWindowPairs_card_ge_crossing_masses
    (houter : ∀ vertex, R.fullGraph.Reachable R.source vertex)
    (configuration : Fin outerEdges → Configuration innerEdges)
    (hcrossing : ∀ edge, S.crosses (configuration edge) = true)
    (first second : Fin outerEdges) (lower upper : ℝ)
    (hwindow : ∀ u v : S.InteriorVertex,
      lower ≤ ((R.substitute S).fullGraph.dist (R.cellEmbedding S first u.val)
        (R.cellEmbedding S second v.val) : ℝ) ∧
      ((R.substitute S).fullGraph.dist (R.cellEmbedding S first u.val)
        (R.cellEmbedding S second v.val) : ℝ) ≤ upper) :
    S.internalSelectedMass true false (configuration first) *
        S.internalSelectedMass true false (configuration second) ≤
      ((R.substitute S).connectedDistanceWindowPairs
        (substitutionConfigurationEquiv configuration) lower upper).card := by
  have hsubset : ((S.internalSourceVertices (configuration first)).product
      (S.internalSourceVertices (configuration second))).map (R.interiorPairEmbedding S first second) ⊆
      (R.substitute S).connectedDistanceWindowPairs
        (substitutionConfigurationEquiv configuration) lower upper := by
    intro pair hpair
    obtain ⟨pair, hchildPair, rfl⟩ := Finset.mem_map.mp hpair
    obtain ⟨hu, hv⟩ := Finset.mem_product.mp hchildPair
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hwindow pair.1 pair.2⟩, ?_⟩
    exact R.all_crossing_cells_join_sources S houter configuration hcrossing first second _ _
      (by simpa only [SimpleGraph.reachableDecide_eq_true] using (Finset.mem_filter.mp hu).2)
      (by simpa only [SimpleGraph.reachableDecide_eq_true] using (Finset.mem_filter.mp hv).2)
  have hcard := Finset.card_le_card hsubset
  rw [Finset.card_map] at hcard
  have hproduct : ((S.internalSourceVertices (configuration first)).product
      (S.internalSourceVertices (configuration second))).card =
      S.internalSelectedMass true false (configuration first) *
        S.internalSelectedMass true false (configuration second) := by
    exact (Finset.card_product (S.internalSourceVertices (configuration first))
      (S.internalSourceVertices (configuration second))).trans
        (congrArg₂ (fun a b : ℕ => a * b) (S.internalSourceVertices_card (configuration first))
          (S.internalSourceVertices_card (configuration second)))
  exact hproduct.symm.le.trans hcard

end
end Universality.FiniteNetwork
