import Universality.Percolation.Russo

namespace Universality.FiniteNetwork

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem openGraph_le_update_true (ω : Configuration edges) (edge : Fin edges) :
    R.openGraph ω ≤ R.openGraph (Function.update ω edge true) := by
  intro u v hadj
  obtain ⟨hne, other, hopen, hpair⟩ := hadj
  refine ⟨hne, other, ?_, hpair⟩
  by_cases h : other = edge
  · subst other
    simp
  · simpa [Function.update_of_ne h] using hopen

def reachableAfterOpening (ω : Configuration edges) (edge : Fin edges)
    (root v : Fin vertices) : Prop :=
  (R.openGraph ω).Reachable root v ∨
    ((R.openGraph ω).Reachable root (R.endpoint edge).1 ∧
      (R.openGraph ω).Reachable (R.endpoint edge).2 v) ∨
    ((R.openGraph ω).Reachable root (R.endpoint edge).2 ∧
      (R.openGraph ω).Reachable (R.endpoint edge).1 v)

theorem reachableAfterOpening_old_adj (ω : Configuration edges) (edge : Fin edges)
    (root : Fin vertices) {u v : Fin vertices} (hadj : (R.openGraph ω).Adj u v)
    (hu : R.reachableAfterOpening ω edge root u) : R.reachableAfterOpening ω edge root v := by
  rcases hu with h | ⟨hroot, hcell⟩ | ⟨hroot, hcell⟩
  · exact Or.inl (h.trans hadj.reachable)
  · exact Or.inr (Or.inl ⟨hroot, hcell.trans hadj.reachable⟩)
  · exact Or.inr (Or.inr ⟨hroot, hcell.trans hadj.reachable⟩)

theorem reachableAfterOpening_first_second (ω : Configuration edges) (edge : Fin edges)
    (root : Fin vertices)
    (hu : R.reachableAfterOpening ω edge root (R.endpoint edge).1) :
    R.reachableAfterOpening ω edge root (R.endpoint edge).2 := by
  rcases hu with h | ⟨hroot, _⟩ | ⟨hroot, _⟩
  · exact Or.inr (Or.inl ⟨h, .refl _⟩)
  · exact Or.inr (Or.inl ⟨hroot, .refl _⟩)
  · exact Or.inl hroot

theorem reachableAfterOpening_second_first (ω : Configuration edges) (edge : Fin edges)
    (root : Fin vertices)
    (hu : R.reachableAfterOpening ω edge root (R.endpoint edge).2) :
    R.reachableAfterOpening ω edge root (R.endpoint edge).1 := by
  rcases hu with h | ⟨hroot, _⟩ | ⟨hroot, _⟩
  · exact Or.inr (Or.inr ⟨h, .refl _⟩)
  · exact Or.inl hroot
  · exact Or.inr (Or.inr ⟨hroot, .refl _⟩)

theorem reachableAfterOpening_adj (ω : Configuration edges) (edge : Fin edges)
    (root : Fin vertices) {u v : Fin vertices}
    (hadj : (R.openGraph (Function.update ω edge true)).Adj u v)
    (hu : R.reachableAfterOpening ω edge root u) : R.reachableAfterOpening ω edge root v := by
  obtain ⟨hne, other, hopen, hpair⟩ := hadj
  by_cases h : other = edge
  · subst other
    rcases hpair with hpair | hpair
    · have hu' : R.reachableAfterOpening ω edge root (R.endpoint edge).1 := by simpa [hpair] using hu
      simpa [hpair] using R.reachableAfterOpening_first_second ω edge root hu'
    · have hu' : R.reachableAfterOpening ω edge root (R.endpoint edge).2 := by simpa [hpair] using hu
      simpa [hpair] using R.reachableAfterOpening_second_first ω edge root hu'
  · apply R.reachableAfterOpening_old_adj ω edge root _ hu
    exact ⟨hne, other, by simpa [Function.update_of_ne h] using hopen, hpair⟩

theorem reachable_update_true_iff (ω : Configuration edges) (edge : Fin edges)
    (root v : Fin vertices) :
    (R.openGraph (Function.update ω edge true)).Reachable root v ↔
      R.reachableAfterOpening ω edge root v := by
  constructor
  · rintro ⟨walk⟩
    have propagate {u v : Fin vertices}
        (walk : (R.openGraph (Function.update ω edge true)).Walk u v) :
        R.reachableAfterOpening ω edge root u → R.reachableAfterOpening ω edge root v := by
      induction walk with
      | nil => exact id
      | cons hadj walk ih => exact fun hu => ih (R.reachableAfterOpening_adj ω edge root hadj hu)
    exact propagate walk (Or.inl (.refl _))
  · have hadj : (R.openGraph (Function.update ω edge true)).Adj (R.endpoint edge).1 (R.endpoint edge).2 :=
      ⟨R.loopless edge, edge, by simp, Or.inl rfl⟩
    intro h
    rcases h with h | ⟨hroot, hcell⟩ | ⟨hroot, hcell⟩
    · exact h.mono (R.openGraph_le_update_true ω edge)
    · exact ((hroot.mono (R.openGraph_le_update_true ω edge)).trans hadj.reachable).trans
        (hcell.mono (R.openGraph_le_update_true ω edge))
    · exact ((hroot.mono (R.openGraph_le_update_true ω edge)).trans hadj.symm.reachable).trans
        (hcell.mono (R.openGraph_le_update_true ω edge))

theorem pivotal_of_disconnected_iff (ω : Configuration edges) (edge : Fin edges)
    (hdisconnected : R.crosses ω = false) :
    R.pivotal ω edge = true ↔
      ((R.openGraph ω).Reachable R.source (R.endpoint edge).1 ∧
        (R.openGraph ω).Reachable R.target (R.endpoint edge).2) ∨
      ((R.openGraph ω).Reachable R.source (R.endpoint edge).2 ∧
        (R.openGraph ω).Reachable R.target (R.endpoint edge).1) := by
  have hnot : ¬ (R.openGraph ω).Reachable R.source R.target := by
    intro h
    have hc := (R.crosses_eq_true ω).mpr h
    rw [hdisconnected] at hc
    contradiction
  have hfalse : R.crosses (Function.update ω edge false) = false := by
    apply Bool.eq_false_iff.mpr
    intro hcross
    have h := R.crosses_mono (Function.update ω edge false) ω (by
      intro other hopen
      by_cases heq : other = edge
      · subst other
        simp at hopen
      · simpa [Function.update_of_ne heq] using hopen) hcross
    rw [hdisconnected] at h
    contradiction
  simp only [pivotal, hfalse, Bool.not_false, Bool.and_true, crosses_eq_true,
    reachable_update_true_iff, reachableAfterOpening, hnot, false_or]
  constructor
  · rintro (⟨hs, ht⟩ | ⟨hs, ht⟩)
    · exact Or.inl ⟨hs, ht.symm⟩
    · exact Or.inr ⟨hs, ht.symm⟩
  · rintro (⟨hs, ht⟩ | ⟨hs, ht⟩)
    · exact Or.inl ⟨hs, ht.symm⟩
    · exact Or.inr ⟨hs, ht.symm⟩

end Universality.FiniteNetwork
