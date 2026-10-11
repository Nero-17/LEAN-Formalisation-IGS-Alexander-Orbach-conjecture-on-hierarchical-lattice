import Universality.Percolation.ConfigurationEncoding

/-!
# Locally checkable certificates for finite connected components

An external search may propose a bit mask, a rank, and a parent edge for every
vertex.  The checker only checks open edges and decreasing ranks.  The theorem
below proves that passing this checker identifies the actual graph component.
No external search result is trusted.
-/

namespace Universality.FiniteNetwork

structure ConnectivityCertificate (vertices edges : ℕ) where
  mask : BitVec vertices
  rank : Fin vertices → ℕ
  parent : Fin vertices → Fin edges

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def ConnectivityCertificate.Valid (certificate : ConnectivityCertificate vertices edges)
    (ω : Configuration edges) (root : Fin vertices) : Prop :=
  certificate.mask.getLsbD root.val = true ∧
  (∀ e, ω e = true →
    certificate.mask.getLsbD (R.endpoint e).1.val =
      certificate.mask.getLsbD (R.endpoint e).2.val) ∧
  (∀ v, certificate.mask.getLsbD v.val = true → v ≠ root →
    ω (certificate.parent v) = true ∧
      ((v = (R.endpoint (certificate.parent v)).1 ∧
        certificate.mask.getLsbD (R.endpoint (certificate.parent v)).2.val = true ∧
        certificate.rank (R.endpoint (certificate.parent v)).2 < certificate.rank v) ∨
       (v = (R.endpoint (certificate.parent v)).2 ∧
        certificate.mask.getLsbD (R.endpoint (certificate.parent v)).1.val = true ∧
        certificate.rank (R.endpoint (certificate.parent v)).1 < certificate.rank v)))

instance (certificate : ConnectivityCertificate vertices edges)
    (ω : Configuration edges) (root : Fin vertices) :
    Decidable (certificate.Valid R ω root) := by
  unfold ConnectivityCertificate.Valid
  infer_instance

theorem ConnectivityCertificate.reachable_iff
    (certificate : ConnectivityCertificate vertices edges)
    (ω : Configuration edges) (root : Fin vertices)
    (valid : certificate.Valid R ω root) (v : Fin vertices) :
    (R.openGraph ω).Reachable root v ↔ certificate.mask.getLsbD v.val = true := by
  obtain ⟨hroot, hclosed, hparent⟩ := valid
  constructor
  · rintro ⟨walk⟩
    have propagate {a b : Fin vertices} (walk : (R.openGraph ω).Walk a b) :
        certificate.mask.getLsbD a.val = true → certificate.mask.getLsbD b.val = true := by
      induction walk with
      | nil => exact id
      | @cons a b c hadj walk ih =>
          intro ha
          apply ih
          obtain ⟨_, e, he, huv | hvu⟩ := hadj
          · have h := hclosed e he
            rw [huv] at h
            exact h ▸ ha
          · have h := hclosed e he
            rw [hvu] at h
            exact h.symm ▸ ha
    exact propagate walk hroot
  · intro hin
    have descend : ∀ n, ∀ v : Fin vertices, certificate.rank v = n →
        certificate.mask.getLsbD v.val = true → (R.openGraph ω).Reachable root v := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro v hr hv
          by_cases heq : v = root
          · subst v
            exact .refl root
          · obtain ⟨hopen, hfirst | hsecond⟩ := hparent v hv heq
            · obtain ⟨hfirst, hmask, hrank⟩ := hfirst
              have hreach := ih _ (hr ▸ hrank) _ rfl hmask
              apply hreach.trans
              apply SimpleGraph.Adj.reachable
              change _ ≠ _ ∧ ∃ e, _
              refine ⟨?_, certificate.parent v, hopen, Or.inr ?_⟩
              · intro h
                exact (R.loopless (certificate.parent v)).symm (h.trans hfirst)
              · exact Prod.ext hfirst.symm rfl
            · obtain ⟨hsecond, hmask, hrank⟩ := hsecond
              have hreach := ih _ (hr ▸ hrank) _ rfl hmask
              apply hreach.trans
              apply SimpleGraph.Adj.reachable
              change _ ≠ _ ∧ ∃ e, _
              refine ⟨?_, certificate.parent v, hopen, Or.inl ?_⟩
              · intro h
                exact R.loopless (certificate.parent v) (h.trans hsecond)
              · exact Prod.ext rfl hsecond.symm
    exact descend _ v rfl hin

theorem ConnectivityCertificate.reachableDecide_eq
    (certificate : ConnectivityCertificate vertices edges)
    (ω : Configuration edges) (root : Fin vertices)
    (valid : certificate.Valid R ω root) (v : Fin vertices) :
    (R.openGraph ω).reachableDecide root v = certificate.mask.getLsbD v.val := by
  apply Bool.eq_iff_iff.mpr
  rw [SimpleGraph.reachableDecide_eq_true]
  exact certificate.reachable_iff R ω root valid v

end Universality.FiniteNetwork
