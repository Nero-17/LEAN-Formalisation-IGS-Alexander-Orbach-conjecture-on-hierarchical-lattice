import Universality.Graph.SubstitutionNetwork

namespace Universality.FiniteNetwork
noncomputable section
variable {vR eR vS eS : ℕ} {R : FiniteNetwork vR eR} {S : FiniteNetwork vS eS}

/-- A relabelling preserving both terminals and the ordered endpoints of every
indexed edge. Orientation-preserving relabellings suffice for associativity. -/
structure NetworkEquivalence (R : FiniteNetwork vR eR) (S : FiniteNetwork vS eS) where
  vertex : Fin vR ≃ Fin vS
  edge : Fin eR ≃ Fin eS
  source : vertex R.source = S.source
  target : vertex R.target = S.target
  endpoint : ∀ e, S.endpoint (edge e) = (vertex (R.endpoint e).1, vertex (R.endpoint e).2)

namespace NetworkEquivalence

def refl (R : FiniteNetwork vR eR) : R.NetworkEquivalence R where
  vertex := Equiv.refl _
  edge := Equiv.refl _
  source := rfl
  target := rfl
  endpoint _ := rfl

def symm (equivalence : R.NetworkEquivalence S) : S.NetworkEquivalence R where
  vertex := equivalence.vertex.symm
  edge := equivalence.edge.symm
  source := equivalence.vertex.symm_apply_eq.mpr equivalence.source.symm
  target := equivalence.vertex.symm_apply_eq.mpr equivalence.target.symm
  endpoint e := by
    have h := equivalence.endpoint (equivalence.edge.symm e)
    simp only [Equiv.apply_symm_apply] at h
    apply Prod.ext
    · apply equivalence.vertex.injective
      simpa only [Equiv.apply_symm_apply] using (congrArg Prod.fst h).symm
    · apply equivalence.vertex.injective
      simpa only [Equiv.apply_symm_apply] using (congrArg Prod.snd h).symm

def trans {vT eT : ℕ} {T : FiniteNetwork vT eT}
    (first : R.NetworkEquivalence S) (second : S.NetworkEquivalence T) : R.NetworkEquivalence T where
  vertex := first.vertex.trans second.vertex
  edge := first.edge.trans second.edge
  source := by simp only [Equiv.trans_apply, first.source, second.source]
  target := by simp only [Equiv.trans_apply, first.target, second.target]
  endpoint e := by simp only [Equiv.trans_apply, second.endpoint, first.endpoint]

def configuration (equivalence : R.NetworkEquivalence S) : Configuration eR ≃ Configuration eS where
  toFun configuration e := configuration (equivalence.edge.symm e)
  invFun configuration e := configuration (equivalence.edge e)
  left_inv configuration := by funext e; simp
  right_inv configuration := by funext e; simp

theorem bernoulliWeight (equivalence : R.NetworkEquivalence S) (p : ℝ) (ω : Configuration eR) :
    FiniteNetwork.bernoulliWeight p (equivalence.configuration ω) = FiniteNetwork.bernoulliWeight p ω := by
  unfold FiniteNetwork.bernoulliWeight
  exact equivalence.edge.symm.prod_comp (fun e => if ω e then p else 1 - p)

def openGraphIso (equivalence : R.NetworkEquivalence S) (ω : Configuration eR) :
    R.openGraph ω ≃g S.openGraph (equivalence.configuration ω) where
  toEquiv := equivalence.vertex
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨hne, e, he, hpair⟩
      refine ⟨fun h => hne (congrArg equivalence.vertex h), equivalence.edge.symm e, he, ?_⟩
      have h := equivalence.endpoint (equivalence.edge.symm e)
      simp only [Equiv.apply_symm_apply] at h
      rcases hpair with hpair | hpair
      · left
        apply Prod.ext <;> apply equivalence.vertex.injective
        · exact (congrArg Prod.fst h).symm.trans (congrArg Prod.fst hpair)
        · exact (congrArg Prod.snd h).symm.trans (congrArg Prod.snd hpair)
      · right
        apply Prod.ext <;> apply equivalence.vertex.injective
        · exact (congrArg Prod.fst h).symm.trans (congrArg Prod.fst hpair)
        · exact (congrArg Prod.snd h).symm.trans (congrArg Prod.snd hpair)
    · rintro ⟨hne, e, he, hpair | hpair⟩
      · refine ⟨fun h => hne (equivalence.vertex.injective h), equivalence.edge e, ?_, Or.inl ?_⟩
        · simpa only [configuration, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using he
        · rw [equivalence.endpoint, hpair]
      · refine ⟨fun h => hne (equivalence.vertex.injective h), equivalence.edge e, ?_, Or.inr ?_⟩
        · simpa only [configuration, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using he
        · rw [equivalence.endpoint, hpair]

theorem crosses (equivalence : R.NetworkEquivalence S) (ω : Configuration eR) :
    S.crosses (equivalence.configuration ω) = R.crosses ω := by
  apply Bool.eq_iff_iff.mpr
  rw [S.crosses_eq_true, R.crosses_eq_true, ← equivalence.source, ← equivalence.target]
  exact (equivalence.openGraphIso ω).reachable_iff

theorem reliability (equivalence : R.NetworkEquivalence S) (p : ℝ) : S.reliability p = R.reliability p := by
  unfold FiniteNetwork.reliability
  rw [← equivalence.configuration.sum_comp]
  simp only [equivalence.crosses, equivalence.bernoulliWeight]

end NetworkEquivalence
end
end Universality.FiniteNetwork
