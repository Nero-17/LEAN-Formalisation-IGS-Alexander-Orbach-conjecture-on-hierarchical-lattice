import Universality.Graph.EdgeOpening
import Universality.Percolation.ConditionalPivotal
import Universality.Percolation.LocalMassResponse

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def pivotalRowCorrection : LiveState → ℝ
  | .connected => 0
  | .both => 1
  | .single => -2

theorem source_target_disjoint_of_disconnected (ω : Configuration edges)
    (hdisconnected : R.crosses ω = false) (v : Fin vertices) :
    ¬ ((R.openGraph ω).reachableDecide R.source v = true ∧
      (R.openGraph ω).reachableDecide R.target v = true) := by
  rintro ⟨hs, ht⟩
  have h := ((R.openGraph ω).reachableDecide_eq_true R.source v).mp hs
  have h' := ((R.openGraph ω).reachableDecide_eq_true R.target v).mp ht
  have hcross := (R.crosses_eq_true ω).mpr (h.trans h'.symm)
  rw [hdisconnected] at hcross
  contradiction

theorem active_single (ω : Configuration edges) (v : Fin vertices) :
    R.active .single ω v = (R.openGraph ω).reachableDecide R.source v := by
  simp only [active, show (LiveState.single == LiveState.both) = false from by decide,
    Bool.false_and, Bool.or_false]

theorem active_reverse_single (ω : Configuration edges) (v : Fin vertices) :
    R.reverse.active .single ω v = (R.openGraph ω).reachableDecide R.target v := by
  rw [active_single]
  rfl

theorem active_both (ω : Configuration edges) (v : Fin vertices) :
    R.active .both ω v = ((R.openGraph ω).reachableDecide R.source v ||
      (R.openGraph ω).reachableDecide R.target v) := by
  simp only [active, beq_self_eq_true, Bool.true_and]

theorem pivotal_bridge_bool (ω : Configuration edges) (edge : Fin edges)
    (hdisconnected : R.crosses ω = false) :
    R.pivotal ω edge =
      (((R.openGraph ω).reachableDecide R.source (R.endpoint edge).1 &&
        (R.openGraph ω).reachableDecide R.target (R.endpoint edge).2) ||
       ((R.openGraph ω).reachableDecide R.source (R.endpoint edge).2 &&
        (R.openGraph ω).reachableDecide R.target (R.endpoint edge).1)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, Bool.and_eq_true, SimpleGraph.reachableDecide_eq_true]
  exact R.pivotal_of_disconnected_iff ω edge hdisconnected

set_option maxHeartbeats 1000000 in
theorem childState_row_identity (ω : Configuration edges) (edge : Fin edges)
    (hdisconnected : R.crosses ω = false) (τ : LiveState) :
    (if R.childState .both ω edge = some τ then (1 : ℝ) else 0) =
      (if R.childState .single ω edge = some τ then 1 else 0) +
      (if R.reverse.childState .single ω edge = some τ then 1 else 0) +
        pivotalRowCorrection τ * (if R.pivotal ω edge then 1 else 0) := by
  have hfirst := R.source_target_disjoint_of_disconnected ω hdisconnected (R.endpoint edge).1
  have hsecond := R.source_target_disjoint_of_disconnected ω hdisconnected (R.endpoint edge).2
  have hopen : ω edge = true →
      (R.openGraph ω).reachableDecide R.source (R.endpoint edge).1 =
        (R.openGraph ω).reachableDecide R.source (R.endpoint edge).2 := by
    intro he
    simpa only [active_single] using R.active_endpoints_eq_of_open .single ω edge he
  have hopen' : ω edge = true →
      (R.openGraph ω).reachableDecide R.target (R.endpoint edge).1 =
        (R.openGraph ω).reachableDecide R.target (R.endpoint edge).2 := by
    intro he
    simpa only [active_reverse_single, reverse_endpoint] using
      R.reverse.active_endpoints_eq_of_open .single ω edge he
  rw [R.pivotal_bridge_bool ω edge hdisconnected]
  simp only [childState, reverse_endpoint]
  simp only [active_reverse_single]
  simp only [active_single, active_both]
  cases ha : (R.openGraph ω).reachableDecide R.source (R.endpoint edge).1 <;>
    cases hb : (R.openGraph ω).reachableDecide R.source (R.endpoint edge).2 <;>
    cases hc : (R.openGraph ω).reachableDecide R.target (R.endpoint edge).1 <;>
    cases hd : (R.openGraph ω).reachableDecide R.target (R.endpoint edge).2 <;>
    cases he : ω edge <;> cases τ <;> norm_num [pivotalRowCorrection] <;> simp_all

theorem liveCount_row_identity (ω : Configuration edges)
    (hdisconnected : R.crosses ω = false) (τ : LiveState) :
    (R.liveCount .both τ ω : ℝ) =
      (R.liveCount .single τ ω : ℝ) + (R.reverse.liveCount .single τ ω : ℝ) +
        pivotalRowCorrection τ * R.pivotalCount ω := by
  simp only [liveCount, Finset.card_eq_sum_ones, Finset.sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero, pivotalCount_as_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro edge _
  exact R.childState_row_identity ω edge hdisconnected τ

end
end Universality.FiniteNetwork
