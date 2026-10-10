import Universality.Graph.SubstitutionNetwork
import Mathlib.Combinatorics.SimpleGraph.Metric
import Mathlib.Tactic.Linarith

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def fullGraph : SimpleGraph (Fin vertices) := R.openGraph (fun _ => true)

instance : DecidableRel R.fullGraph.Adj :=
  inferInstanceAs (DecidableRel (R.openGraph (fun _ => true)).Adj)

/-- A shortest-path certificate: an explicit walk gives the upper bound,
and an integer-valued one-Lipschitz height gives the lower bound. -/
structure DistanceCertificate where
  length : ℕ
  height : Fin vertices → ℤ
  source_height : height R.source = 0
  target_height : height R.target = length
  edge_bound : ∀ edge, |height (R.endpoint edge).1 - height (R.endpoint edge).2| ≤ 1
  walk : R.fullGraph.Walk R.source R.target
  walk_length : walk.length = length

theorem height_difference_le_walk_length (height : Fin vertices → ℤ)
    (hbound : ∀ edge, |height (R.endpoint edge).1 - height (R.endpoint edge).2| ≤ 1)
    {u v : Fin vertices} (walk : R.fullGraph.Walk u v) :
    |height u - height v| ≤ (walk.length : ℤ) := by
  induction walk with
  | nil => simp
  | @cons u v w hadj walk ih =>
      have hstep : |height u - height v| ≤ 1 := by
        obtain ⟨_, edge, _, h | h⟩ := hadj
        · simpa only [h] using hbound edge
        · simpa only [h, abs_sub_comm] using hbound edge
      have htriangle := abs_add_le (height u - height v) (height v - height w)
      have hcancel : height u - height v + (height v - height w) = height u - height w := by ring
      rw [hcancel] at htriangle
      simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
      linarith

theorem DistanceCertificate.distance_eq (certificate : R.DistanceCertificate) :
    R.fullGraph.dist R.source R.target = certificate.length := by
  apply Nat.le_antisymm
  · simpa only [certificate.walk_length] using SimpleGraph.dist_le certificate.walk
  · have reachable : R.fullGraph.Reachable R.source R.target := ⟨certificate.walk⟩
    obtain ⟨shortest, hlength⟩ := reachable.exists_walk_length_eq_dist
    have h := R.height_difference_le_walk_length certificate.height certificate.edge_bound shortest
    rw [certificate.source_height, certificate.target_height, hlength] at h
    simpa using h

def DistanceCertificate.ofReachable (reachable : R.fullGraph.Reachable R.source R.target) :
    R.DistanceCertificate where
  length := R.fullGraph.dist R.source R.target
  height v := R.fullGraph.dist R.source v
  source_height := by simp
  target_height := rfl
  edge_bound edge := by
    have hadj : R.fullGraph.Adj (R.endpoint edge).1 (R.endpoint edge).2 :=
      ⟨R.loopless edge, edge, rfl, Or.inl rfl⟩
    have hforward := hadj.reachable.dist_triangle_right R.source
    have hbackward := hadj.symm.reachable.dist_triangle_right R.source
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj] at hforward
    rw [SimpleGraph.dist_eq_one_iff_adj.mpr hadj.symm] at hbackward
    rw [abs_le]
    constructor <;> omega
  walk := Classical.choose reachable.exists_walk_length_eq_dist
  walk_length := Classical.choose_spec reachable.exists_walk_length_eq_dist

end
end Universality.FiniteNetwork
