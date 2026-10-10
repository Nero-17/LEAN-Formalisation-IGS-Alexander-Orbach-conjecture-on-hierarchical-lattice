import Universality.Percolation.RefinementVertexMean
import Universality.Percolation.PopulationMartingale
import Mathlib.Probability.Martingale.Centering

namespace Universality.Rule.ConfigurationHistory
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem vertexMass_stronglyAdapted (rule : Rule) (state : LiveState) :
    StronglyAdapted Filtration.piLE (vertexMass rule state) :=
  history_observables_stronglyAdapted rule (fun n history =>
    ((rule.generation n).network.internalSelectedMass true (state == .both) (latest rule n history) : ℝ))

theorem vertexMass_condExp (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source) (state : LiveState) (n : ℕ) :
    (infiniteLaw rule p hp hp' hfixed (state == .connected))[vertexMass rule state (n + 1) | Filtration.piLE n]
      =ᵐ[infiniteLaw rule p hp hp' hfixed (state == .connected)] fun path =>
        vertexMass rule state n path + weightedPopulation rule state (rule.network.conditionalVertexMass p) n (path n) := by
  apply (infiniteLaw_condExp rule p hp hp' hfixed (state == .connected) n
    (fun next => ((rule.generation (n + 1)).network.internalSelectedMass true
      (state == .both) (latest rule (n + 1) next) : ℝ))).trans
  exact Filter.Eventually.of_forall (fun path =>
    refinementWeight_vertexMass rule p hp hp' hfixed symmetry hs ht n (latest rule n (path n)) state)

theorem vertexMass_increment_condExp (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source) (state : LiveState) (n : ℕ) :
    (infiniteLaw rule p hp hp' hfixed (state == .connected))[
      vertexMass rule state (n + 1) - vertexMass rule state n | Filtration.piLE n]
      =ᵐ[infiniteLaw rule p hp hp' hfixed (state == .connected)] fun path =>
        weightedPopulation rule state (rule.network.conditionalVertexMass p) n (path n) := by
  have hint (k : ℕ) := (memLp_vertexMass rule p hp hp' hfixed state k 1).integrable le_rfl
  apply (condExp_sub (hint (n + 1)) (hint n) (Filtration.piLE n)).trans
  have hcurrent := condExp_of_stronglyMeasurable (Filtration.piLE.le n)
    (vertexMass_stronglyAdapted rule state n) (hint n)
  filter_upwards [vertexMass_condExp rule p hp hp' hfixed symmetry hs ht state n] with path hpath
  simp only [Pi.sub_apply, hcurrent, hpath]
  ring

/-- The predictable accumulated reward is the sum of the actual live-cell responses. -/
theorem vertexMass_predictablePart (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (symmetry : rule.network.NetworkSymmetry)
    (hs : symmetry.vertex rule.network.source = rule.network.target)
    (ht : symmetry.vertex rule.network.target = rule.network.source) (state : LiveState) (n : ℕ) :
    predictablePart (vertexMass rule state) Filtration.piLE
      (infiniteLaw rule p hp hp' hfixed (state == .connected)) n
      =ᵐ[infiniteLaw rule p hp hp' hfixed (state == .connected)] fun path =>
        ∑ k ∈ Finset.range n, weightedPopulation rule state (rule.network.conditionalVertexMass p) k (path k) := by
  unfold predictablePart
  have hall := ae_all_iff.mpr (fun k =>
    vertexMass_increment_condExp rule p hp hp' hfixed symmetry hs ht state k)
  filter_upwards [hall] with path hpath
  simp only [Finset.sum_apply]
  exact Finset.sum_congr rfl (fun k _ => hpath k)

theorem vertexMass_martingalePart (rule : Rule) (p : ℝ) (hp : 0 < p) (hp' : p < 1)
    (hfixed : rule.network.reliability p = p) (state : LiveState) :
    Martingale (martingalePart (vertexMass rule state) Filtration.piLE
      (infiniteLaw rule p hp hp' hfixed (state == .connected))) Filtration.piLE
      (infiniteLaw rule p hp hp' hfixed (state == .connected)) :=
  martingale_martingalePart (vertexMass_stronglyAdapted rule state)
    (fun n => (memLp_vertexMass rule p hp hp' hfixed state n 1).integrable le_rfl)

end
end Universality.Rule.ConfigurationHistory
