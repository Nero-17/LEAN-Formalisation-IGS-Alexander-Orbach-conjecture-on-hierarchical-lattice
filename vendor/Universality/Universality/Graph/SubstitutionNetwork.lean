import Universality.Percolation.SubstitutionMass
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Logic.Equiv.Fin.Basic

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges innerVertices innerEdges : ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : FiniteNetwork innerVertices innerEdges)

instance : Fintype S.InteriorVertex := by
  unfold InteriorVertex
  infer_instance

instance : DecidableEq S.InteriorVertex := by
  unfold InteriorVertex
  infer_instance

instance : Fintype (R.SubstitutionVertex S) := by
  unfold SubstitutionVertex
  infer_instance

instance : DecidableEq (R.SubstitutionVertex S) := by
  unfold SubstitutionVertex
  infer_instance

def substitute : FiniteNetwork (Fintype.card (R.SubstitutionVertex S)) (outerEdges * innerEdges) where
  endpoint edge :=
    let pair := finProdFinEquiv.symm edge
    (Fintype.equivFin _ (R.cellVertex S pair.1 (S.endpoint pair.2).1),
     Fintype.equivFin _ (R.cellVertex S pair.1 (S.endpoint pair.2).2))
  source := Fintype.equivFin _ (Sum.inl R.source)
  target := Fintype.equivFin _ (Sum.inl R.target)
  terminals_distinct := by
    intro h
    exact R.terminals_distinct (Sum.inl.inj ((Fintype.equivFin _).injective h))
  loopless edge := by
    intro h
    exact S.loopless (finProdFinEquiv.symm edge).2
      (R.cellVertex_injective S _ ((Fintype.equivFin _).injective h))

def substitutionConfigurationEquiv :
    (Fin outerEdges → Configuration innerEdges) ≃ Configuration (outerEdges * innerEdges) where
  toFun ω edge := ω (finProdFinEquiv.symm edge).1 (finProdFinEquiv.symm edge).2
  invFun ω edge child := ω (finProdFinEquiv (edge, child))
  left_inv ω := by funext edge child; simp
  right_inv ω := by
    funext edge
    change ω (finProdFinEquiv (finProdFinEquiv.symm edge)) = ω edge
    rw [Equiv.apply_symm_apply]

theorem substitute_endpoint (edge : Fin outerEdges) (child : Fin innerEdges) :
    (R.substitute S).endpoint (finProdFinEquiv (edge, child)) =
      (Fintype.equivFin _ (R.cellVertex S edge (S.endpoint child).1),
       Fintype.equivFin _ (R.cellVertex S edge (S.endpoint child).2)) := by
  simp only [substitute, Equiv.symm_apply_apply]

def substitutionGraphIso (ω : Fin outerEdges → Configuration innerEdges) :
    R.substitutedGraph S ω ≃g
      (R.substitute S).openGraph (substitutionConfigurationEquiv ω) where
  toEquiv := Fintype.equivFin _
  map_rel_iff' := by
    intro u v
    constructor
    · rintro ⟨hne, edge, hopen, hpair | hpair⟩
      · refine ⟨fun h => hne (congrArg (Fintype.equivFin _) h),
          (finProdFinEquiv.symm edge).1,
          (S.endpoint (finProdFinEquiv.symm edge).2).1,
          (S.endpoint (finProdFinEquiv.symm edge).2).2, ?_, ?_, ?_⟩
        · exact ⟨S.loopless _, _, hopen, Or.inl rfl⟩
        · exact (Fintype.equivFin _).injective (congrArg Prod.fst hpair)
        · exact (Fintype.equivFin _).injective (congrArg Prod.snd hpair)
      · refine ⟨fun h => hne (congrArg (Fintype.equivFin _) h),
          (finProdFinEquiv.symm edge).1,
          (S.endpoint (finProdFinEquiv.symm edge).2).2,
          (S.endpoint (finProdFinEquiv.symm edge).2).1, ?_, ?_, ?_⟩
        · exact ⟨(S.loopless _).symm, _, hopen, Or.inr rfl⟩
        · exact (Fintype.equivFin _).injective (congrArg Prod.snd hpair)
        · exact (Fintype.equivFin _).injective (congrArg Prod.fst hpair)
    · rintro ⟨hne, edge, x, y, hxy, rfl, rfl⟩
      obtain ⟨_, child, hopen, hpair | hpair⟩ := hxy
      · refine ⟨fun h => hne ((Fintype.equivFin _).injective h),
          finProdFinEquiv (edge, child), ?_, Or.inl ?_⟩
        · change ω (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).1
            (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).2 = true
          simpa only [Equiv.symm_apply_apply] using hopen
        · rw [substitute_endpoint, hpair]
      · refine ⟨fun h => hne ((Fintype.equivFin _).injective h),
          finProdFinEquiv (edge, child), ?_, Or.inr ?_⟩
        · change ω (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).1
            (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).2 = true
          simpa only [Equiv.symm_apply_apply] using hopen
        · rw [substitute_endpoint, hpair]

theorem bernoulliWeight_substitutionConfiguration (p : ℝ)
    (ω : Fin outerEdges → Configuration innerEdges) :
    bernoulliWeight p (substitutionConfigurationEquiv ω) = ∏ e, bernoulliWeight p (ω e) := by
  unfold bernoulliWeight
  rw [← Fintype.prod_prod_type
    (fun pair : Fin outerEdges × Fin innerEdges => if ω pair.1 pair.2 then p else 1 - p)]
  exact finProdFinEquiv.symm.prod_comp
    (fun pair : Fin outerEdges × Fin innerEdges => if ω pair.1 pair.2 then p else 1 - p)

theorem substitute_reachable_iff (ω : Fin outerEdges → Configuration innerEdges)
    (u v : R.SubstitutionVertex S) :
    ((R.substitute S).openGraph (substitutionConfigurationEquiv ω)).Reachable
      (Fintype.equivFin _ u) (Fintype.equivFin _ v) ↔
      (R.substitutedGraph S ω).Reachable u v :=
  SimpleGraph.Iso.reachable_iff (φ := R.substitutionGraphIso S ω)

theorem substitute_conditioning (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) :
    (R.substitute S).conditioning σ (substitutionConfigurationEquiv ω) =
      R.substitutedConditioning S σ ω := by
  classical
  have hc : (R.substitute S).crosses (substitutionConfigurationEquiv ω) =
      decide ((R.substitutedGraph S ω).Reachable (Sum.inl R.source) (Sum.inl R.target)) := by
    apply Bool.eq_iff_iff.mpr
    rw [crosses_eq_true, decide_eq_true_eq]
    exact R.substitute_reachable_iff S ω _ _
  cases σ <;> simp only [conditioning, substitutedConditioning, hc]
  all_goals
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.not_eq_true', decide_eq_true_eq, decide_eq_false_iff_not]

theorem substitute_active (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) (v : R.SubstitutionVertex S) :
    (R.substitute S).active σ (substitutionConfigurationEquiv ω) (Fintype.equivFin _ v) =
      R.substitutedActive S σ ω v := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [active, substitutedActive, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true, beq_iff_eq, decide_eq_true_eq]
  exact or_congr (R.substitute_reachable_iff S ω _ _) (and_congr Iff.rfl
    (R.substitute_reachable_iff S ω _ _))

theorem substitute_childState (σ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) (edge : Fin outerEdges) (child : Fin innerEdges) :
    (R.substitute S).childState σ (substitutionConfigurationEquiv ω)
      (finProdFinEquiv (edge, child)) = R.substitutedChildState S σ ω edge child := by
  unfold childState substitutedChildState
  rw [substitute_endpoint, substitute_active, substitute_active]
  have hω : substitutionConfigurationEquiv ω (finProdFinEquiv (edge, child)) = ω edge child := by
    change ω (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).1
      (finProdFinEquiv.symm (finProdFinEquiv (edge, child))).2 = ω edge child
    rw [Equiv.symm_apply_apply]
  rw [hω]

theorem substitute_liveCount (σ τ : LiveState)
    (ω : Fin outerEdges → Configuration innerEdges) :
    (R.substitute S).liveCount σ τ (substitutionConfigurationEquiv ω) =
      R.substitutedLiveCount S σ τ ω := by
  classical
  unfold liveCount substitutedLiveCount
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [← Fintype.sum_prod_type
    (fun pair : Fin outerEdges × Fin innerEdges =>
      if R.substitutedChildState S σ ω pair.1 pair.2 = some τ then 1 else 0)]
  symm
  apply Fintype.sum_equiv finProdFinEquiv
  intro pair
  rw [substitute_childState]

theorem substitute_conditioningProbability (p : ℝ) (σ : LiveState) :
    (R.substitute S).conditioningProbability p σ =
      R.substitutedConditioningProbability S p σ := by
  unfold conditioningProbability substitutedConditioningProbability
  symm
  apply Fintype.sum_equiv substitutionConfigurationEquiv
  intro ω
  rw [substitute_conditioning, bernoulliWeight_substitutionConfiguration]

theorem substitute_massMatrix (p : ℝ) :
    (R.substitute S).massMatrix p = R.substitutedMassMatrix S p := by
  ext σ τ
  unfold massMatrix substitutedMassMatrix
  rw [substitute_conditioningProbability]
  congr 1
  symm
  apply Fintype.sum_equiv substitutionConfigurationEquiv
  intro ω
  rw [substitute_conditioning, bernoulliWeight_substitutionConfiguration, substitute_liveCount]

theorem substitute_reliability (p : ℝ) :
    (R.substitute S).reliability p = R.reliability (S.reliability p) := by
  rw [← conditioningProbability_connected, substitute_conditioningProbability,
    substitutedConditioningProbability_eq, conditioningProbability_connected]

theorem substitute_massMatrix_mul (p : ℝ)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source) :
    (R.substitute S).massMatrix p = R.massMatrix (S.reliability p) * S.massMatrix p := by
  rw [substitute_massMatrix, substitutedMassMatrix_eq_mul R S p hpositive hless symmetry hs ht]

end
end Universality.FiniteNetwork
