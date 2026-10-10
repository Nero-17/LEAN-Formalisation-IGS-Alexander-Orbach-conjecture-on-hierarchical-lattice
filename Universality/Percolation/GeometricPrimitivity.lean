import Universality.Percolation.FiniteMassDimension
import Universality.Matrix.PrimitiveThreeState

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem reachable_onlyClosed_of_walk_avoiding_source (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source)
    {u v : Fin vertices} (walk : R.fullGraph.Walk u v)
    (havoid : R.source ∉ walk.support) :
    (R.openGraph (onlyClosed edge)).Reachable u v := by
  induction walk with
  | nil => exact .refl _
  | @cons u w v hadj tail ih =>
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons, not_or] at havoid
    have hw : R.source ≠ w := fun h => havoid.2 (h ▸ tail.start_mem_support)
    obtain ⟨hne, other, _, hpair⟩ := hadj
    have hother : other ≠ edge := by
      intro h
      subst other
      rcases hpair with hpair | hpair
      · rcases hincident with hfirst | hsecond
        · apply havoid.1
          simpa only [hpair, Prod.fst] using hfirst.symm
        · apply hw
          simpa only [hpair, Prod.snd] using hsecond.symm
      · rcases hincident with hfirst | hsecond
        · apply hw
          simpa only [hpair, Prod.fst] using hfirst.symm
        · apply havoid.1
          simpa only [hpair, Prod.snd] using hsecond.symm
    have hopen : onlyClosed edge other = true := by simp [onlyClosed, hother]
    have hclosedadj : (R.openGraph (onlyClosed edge)).Adj u w := ⟨hne, other, hopen, hpair⟩
    exact hclosedadj.reachable.trans (ih havoid.2)

/-- Choose the first edge of a simple terminal path. After deleting it, the
remaining suffix still reaches the target; another terminal crossing reaches
that suffix from the source. Both endpoints of the deleted edge stay active. -/
theorem exists_closed_edge_both_endpoints_active
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) :
    ∃ edge, R.childState .connected (onlyClosed edge) edge = some .both := by
  obtain ⟨walk, hpath⟩ := hconnected.exists_isPath
  obtain ⟨next, hadj, tail, rfl⟩ := SimpleGraph.Walk.exists_eq_cons_of_ne R.terminals_distinct walk
  ·
    have havoid : R.source ∉ tail.support := by
      have hnodup := hpath.support_nodup
      rw [SimpleGraph.Walk.support_cons, List.nodup_cons] at hnodup
      exact hnodup.1
    obtain ⟨hne, edge, _, hpair⟩ := hadj
    have hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source := by
      rcases hpair with h | h
      · exact Or.inl (congrArg Prod.fst h)
      · exact Or.inr (congrArg Prod.snd h)
    have htail := R.reachable_onlyClosed_of_walk_avoiding_source edge hincident tail havoid
    have hcross := (R.crosses_eq_true _).mp (hcut edge)
    have hnext := hcross.trans htail.symm
    have hsource : R.active .connected (onlyClosed edge) R.source = true := by
      simp [active, SimpleGraph.reachableDecide_eq_true]
    have hnextactive : R.active .connected (onlyClosed edge) next = true := by
      have hbeq : (LiveState.connected == LiveState.both) = false := rfl
      simpa only [active, hbeq, Bool.false_and, Bool.or_false] using
        ((R.openGraph (onlyClosed edge)).reachableDecide_eq_true R.source next).mpr hnext
    have hedgeclosed : onlyClosed edge edge = false := by simp [onlyClosed]
    refine ⟨edge, ?_⟩
    rcases hpair with hpair | hpair <;>
      simp [childState, hpair, hsource, hnextactive, hedgeclosed]

theorem childState_allClosed_both_single (edge : Fin edges)
    (hincident : (R.endpoint edge).1 = R.source ∨ (R.endpoint edge).2 = R.source)
    (hfirst : (R.endpoint edge).1 ≠ R.target) (hsecond : (R.endpoint edge).2 ≠ R.target) :
    R.childState .both (fun _ => false) edge = some .single := by
  have hn := R.loopless edge
  have hbeq : (LiveState.both == LiveState.both) = true := rfl
  simp only [childState, active, hbeq, reachableDecide_all_closed]
  rcases hincident with h | h
  · have hne : R.source ≠ (R.endpoint edge).2 := by simpa only [h] using hn
    simp [h, hne, Ne.symm hsecond, Ne.symm R.terminals_distinct]
  · have hne : R.source ≠ (R.endpoint edge).1 := by simpa only [h] using hn.symm
    simp [h, hne, Ne.symm hfirst, Ne.symm R.terminals_distinct]

/-- An explicit primitivity certificate for the actual conditional mass
matrix. Canonicality and terminal symmetry are not needed for this result. -/
theorem massMatrix_fourth_power_pos (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hconnected : R.fullGraph.Reachable R.source R.target)
    (hscale : 1 < R.fullGraph.dist R.source R.target)
    (hcut : ∀ edge, R.crosses (onlyClosed edge) = true) :
    ∀ σ τ, 0 < (R.massMatrix p ^ 4) σ τ := by
  have hcolumn := (R.massPlaneBlock_pos_of_geometry hp hp' hconnected hscale hcut).2
  apply three_state_fourth_power_pos _ (R.massMatrix_nonneg hp.le hp'.le)
    (hcolumn .connected) _ _ (hcolumn .single)
  · obtain ⟨edge, he⟩ := R.exists_closed_edge_both_endpoints_active hconnected hcut
    exact (R.massMatrix_pos_iff hp hp' .connected .both).mpr
      ⟨onlyClosed edge, edge, hcut edge, he⟩
  · obtain ⟨edge, hincident⟩ := R.exists_source_incident_edge hconnected
    obtain ⟨hfirst, hsecond⟩ := R.incident_endpoints_ne_target edge hincident hscale
    apply (R.massMatrix_pos_iff hp hp' .both .single).mpr
    refine ⟨fun _ => false, edge, ?_,
      R.childState_allClosed_both_single edge hincident hfirst hsecond⟩
    simp only [conditioning, R.crosses_all_closed, Bool.not_false]

end
end Universality.FiniteNetwork
