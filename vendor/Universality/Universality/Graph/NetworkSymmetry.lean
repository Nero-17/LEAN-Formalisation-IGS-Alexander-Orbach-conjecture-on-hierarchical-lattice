import Universality.Percolation.Bernoulli

namespace Universality.FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

/-- An automorphism of the edge-indexed undirected network.  The edge
permutation records the independence-preserving action on configurations. -/
structure NetworkSymmetry where
  vertex : Fin vertices ≃ Fin vertices
  edge : Fin edges ≃ Fin edges
  endpoint : ∀ e,
    R.endpoint (edge e) = (vertex (R.endpoint e).1, vertex (R.endpoint e).2) ∨
    R.endpoint (edge e) = (vertex (R.endpoint e).2, vertex (R.endpoint e).1)

namespace NetworkSymmetry

variable {R}

def inverse (s : R.NetworkSymmetry) : R.NetworkSymmetry where
  vertex := s.vertex.symm
  edge := s.edge.symm
  endpoint e := by
    rcases s.endpoint (s.edge.symm e) with h | h
    · left
      apply Prod.ext
      · apply s.vertex.injective
        simpa only [Equiv.apply_symm_apply] using (congrArg Prod.fst h).symm
      · apply s.vertex.injective
        simpa only [Equiv.apply_symm_apply] using (congrArg Prod.snd h).symm
    · right
      apply Prod.ext
      · apply s.vertex.injective
        simpa only [Equiv.apply_symm_apply] using (congrArg Prod.snd h).symm
      · apply s.vertex.injective
        simpa only [Equiv.apply_symm_apply] using (congrArg Prod.fst h).symm

def configurationEquiv (s : R.NetworkSymmetry) : Configuration edges ≃ Configuration edges where
  toFun ω e := ω (s.edge.symm e)
  invFun ω e := ω (s.edge e)
  left_inv ω := by funext e; simp
  right_inv ω := by funext e; simp

theorem configuration_apply (s : R.NetworkSymmetry) (ω : Configuration edges) (e : Fin edges) :
    s.configurationEquiv ω e = ω (s.edge.symm e) := rfl

theorem inverse_configuration (s : R.NetworkSymmetry) (ω : Configuration edges) :
    s.inverse.configurationEquiv (s.configurationEquiv ω) = ω := by
  funext e
  simp [configuration_apply, inverse]

theorem bernoulliWeight_configuration (s : R.NetworkSymmetry)
    (p : ℝ) (ω : Configuration edges) :
    bernoulliWeight p (s.configurationEquiv ω) = bernoulliWeight p ω := by
  unfold bernoulliWeight
  exact s.edge.symm.prod_comp (fun e => if ω e then p else 1 - p)

def openGraphHom (s : R.NetworkSymmetry) (ω : Configuration edges) :
    R.openGraph ω →g R.openGraph (s.configurationEquiv ω) where
  toFun := s.vertex
  map_rel' := by
    rintro u v ⟨hne, e, he, hpair | hpair⟩
    · refine ⟨fun h => hne (s.vertex.injective h), s.edge e, ?_, ?_⟩
      · simpa only [configuration_apply, Equiv.symm_apply_apply] using he
      · simpa only [hpair] using s.endpoint e
    · refine ⟨fun h => hne (s.vertex.injective h), s.edge e, ?_, ?_⟩
      · simpa only [configuration_apply, Equiv.symm_apply_apply] using he
      · have h := s.endpoint e
        simpa only [hpair, or_comm] using h

theorem reachable_configuration_iff (s : R.NetworkSymmetry)
    (ω : Configuration edges) (u v : Fin vertices) :
    (R.openGraph (s.configurationEquiv ω)).Reachable (s.vertex u) (s.vertex v) ↔
      (R.openGraph ω).Reachable u v := by
  constructor
  · intro h
    have hm := h.map (s.inverse.openGraphHom (s.configurationEquiv ω))
    change (R.openGraph (s.inverse.configurationEquiv (s.configurationEquiv ω))).Reachable
      (s.vertex.symm (s.vertex u)) (s.vertex.symm (s.vertex v)) at hm
    simpa only [inverse_configuration, Equiv.symm_apply_apply] using hm
  · intro h
    exact h.map (s.openGraphHom ω)

theorem crosses_configuration_of_terminal_swap (s : R.NetworkSymmetry)
    (hs : s.vertex R.source = R.target) (ht : s.vertex R.target = R.source)
    (ω : Configuration edges) : R.crosses (s.configurationEquiv ω) = R.crosses ω := by
  apply Bool.eq_iff_iff.mpr
  rw [R.crosses_eq_true, R.crosses_eq_true]
  have h := s.reachable_configuration_iff ω R.target R.source
  rw [hs, ht] at h
  exact h.trans ⟨SimpleGraph.Reachable.symm, SimpleGraph.Reachable.symm⟩

end NetworkSymmetry
end Universality.FiniteNetwork
