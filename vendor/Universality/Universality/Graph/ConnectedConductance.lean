import Universality.Graph.DirichletEnergy
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 800000
variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

theorem adjacent_potential_difference_le_sqrt_energy (potential : Fin vertices → ℝ)
    {first second : Fin vertices} (hadj : R.fullGraph.Adj first second) :
    |potential first - potential second| ≤ Real.sqrt (R.dirichletEnergy potential) := by
  rcases hadj.2 with ⟨edge, _, horientation⟩
  have hterm : (potential (R.endpoint edge).1 - potential (R.endpoint edge).2)^2 ≤ R.dirichletEnergy potential := by
    unfold dirichletEnergy
    exact Finset.single_le_sum (fun j _ => sq_nonneg (potential (R.endpoint j).1 - potential (R.endpoint j).2)) (Finset.mem_univ edge)
  have hsq : (potential first - potential second)^2 ≤ R.dirichletEnergy potential := by
    rcases horientation with heq | heq
    · simpa only [heq] using hterm
    · simpa only [heq, sub_sq_comm] using hterm
  have hsqrt := Real.sq_sqrt (R.dirichletEnergy_nonneg potential)
  have habs := sq_abs (potential first - potential second)
  nlinarith [abs_nonneg (potential first - potential second), Real.sqrt_nonneg (R.dirichletEnergy potential)]

theorem walk_potential_difference_le (potential : Fin vertices → ℝ)
    {first second : Fin vertices} (walk : R.fullGraph.Walk first second) :
    |potential first - potential second| ≤ (walk.length : ℝ) * Real.sqrt (R.dirichletEnergy potential) := by
  induction walk with
  | nil => simp
  | @cons first middle last hadj walk ih =>
    have hstep := R.adjacent_potential_difference_le_sqrt_energy potential hadj
    have htriangle := abs_add_le (potential first - potential middle) (potential middle - potential last)
    have hid : (potential first - potential middle) + (potential middle - potential last) =
        potential first - potential last := by ring
    rw [hid] at htriangle
    simp only [SimpleGraph.Walk.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

theorem unitConductance_pos_of_connected (hconnected : R.fullGraph.Reachable R.source R.target) :
    0 < R.unitConductance := by
  obtain ⟨walk⟩ := hconnected
  have hlength : 0 < walk.length := Nat.pos_of_ne_zero (fun hzero =>
    R.terminals_distinct (walk.eq_of_length_eq_zero hzero))
  have hlengthReal : 0 < (walk.length : ℝ) := by exact_mod_cast hlength
  have hlower : 1 / (walk.length : ℝ)^2 ≤ R.unitConductance := by
    apply R.le_unitConductance
    intro potential hs ht
    have hwalk := R.walk_potential_difference_le potential walk
    rw [hs, ht] at hwalk
    norm_num only [sub_zero, abs_one] at hwalk
    have hsq := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hwalk
    have he := Real.sq_sqrt (R.dirichletEnergy_nonneg potential)
    have hproduct : ((walk.length : ℝ) * Real.sqrt (R.dirichletEnergy potential)) *
        ((walk.length : ℝ) * Real.sqrt (R.dirichletEnergy potential)) =
        (walk.length : ℝ)^2 * R.dirichletEnergy potential := by
      calc
        _ = (walk.length : ℝ)^2 * (Real.sqrt (R.dirichletEnergy potential))^2 := by ring
        _ = _ := by rw [he]
    rw [hproduct] at hsq
    apply (div_le_iff₀ (sq_pos_of_pos hlengthReal)).mpr
    nlinarith
  exact (div_pos (by norm_num) (sq_pos_of_pos hlengthReal)).trans_le hlower

theorem unitEffectiveResistance_pos (hconnected : R.fullGraph.Reachable R.source R.target) :
    0 < R.unitEffectiveResistance hconnected := inv_pos.mpr (R.unitConductance_pos_of_connected hconnected)

end
end Universality.FiniteNetwork
