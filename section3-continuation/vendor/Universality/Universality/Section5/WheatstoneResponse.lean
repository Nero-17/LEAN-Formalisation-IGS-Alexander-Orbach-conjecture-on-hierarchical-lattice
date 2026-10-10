import Universality.Section5.HeterogeneousReliability
import Universality.Percolation.WheatstoneReliability
import Mathlib.Tactic.Ring

namespace Universality.Section5
noncomputable section
open FiniteNetwork

def wheatstoneCrossingPatterns : Finset (Configuration 5) :=
  {![false, false, true, true, false],
   ![false, false, true, true, true],
   ![false, true, true, false, true],
   ![false, true, true, true, false],
   ![false, true, true, true, true],
   ![true, false, false, true, true],
   ![true, false, true, true, false],
   ![true, false, true, true, true],
   ![true, true, false, false, false],
   ![true, true, false, false, true],
   ![true, true, false, true, false],
   ![true, true, false, true, true],
   ![true, true, true, false, false],
   ![true, true, true, false, true],
   ![true, true, true, true, false],
   ![true, true, true, true, true]}

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wheatstoneCrossingPatterns_exact :
    Finset.univ.filter (fun configuration : Configuration 5 => wheatstoneNetwork.crosses configuration) =
      wheatstoneCrossingPatterns := by decide

def wheatstoneProbabilityResponse (a b c : ℝ) : ℝ :=
  (1 - c) * (2 * a * b - a ^ 2 * b ^ 2) + c * (a + b - a * b) ^ 2

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem wheatstoneProbabilityResponse_exact (a b c : ℝ) :
    (∑ configuration : Configuration 5,
      if wheatstoneNetwork.crosses configuration then
        ∏ edge : Fin 5, if configuration edge then ![a,b,b,a,c] edge else 1 - ![a,b,b,a,c] edge
      else 0) = wheatstoneProbabilityResponse a b c := by
  rw [← Finset.sum_filter, wheatstoneCrossingPatterns_exact]
  norm_num [wheatstoneCrossingPatterns, Fin.prod_univ_succ, wheatstoneProbabilityResponse,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four,
    Matrix.head_cons, Matrix.tail_cons]
  ring

def wheatstoneRule (a b c : Rule) : Rule :=
  (⟨4, 5, wheatstoneNetwork⟩ : Rule).heterogeneousSubstitute ![a,b,b,a,c]

theorem wheatstoneRule_edges (a b c : Rule) :
    (wheatstoneRule a b c).edges = 2 * a.edges + 2 * b.edges + c.edges := by
  rw [wheatstoneRule, Rule.heterogeneousSubstitute_edges]
  simp [Fin.sum_univ_succ]
  omega

theorem wheatstoneRule_reliability (a b c : Rule) (p : ℝ) :
    (wheatstoneRule a b c).network.reliability p =
      wheatstoneProbabilityResponse (a.network.reliability p)
        (b.network.reliability p) (c.network.reliability p) := by
  change (wheatstoneNetwork.heterogeneousSubstitute
    (fun edge : Fin 5 => (![a,b,b,a,c] edge).network)).reliability p = _
  rw [FiniteNetwork.heterogeneousSubstitute_reliability]
  convert wheatstoneProbabilityResponse_exact (a.network.reliability p)
    (b.network.reliability p) (c.network.reliability p) using 1
  apply Finset.sum_congr rfl
  intro configuration _
  congr 1

theorem wheatstoneRule_fixed_half (a b c : Rule)
    (a_fixed : a.network.reliability (1 / 2) = 1 / 2)
    (b_fixed : b.network.reliability (1 / 2) = 1 / 2)
    (c_fixed : c.network.reliability (1 / 2) = 1 / 2) :
    (wheatstoneRule a b c).network.reliability (1 / 2) = 1 / 2 := by
  rw [wheatstoneRule_reliability, a_fixed, b_fixed, c_fixed]
  norm_num [wheatstoneProbabilityResponse]

end
end Universality.Section5
