import Universality.Percolation.SubcriticalPopulationSum
import Universality.Percolation.VertexNoiseLimit
import Universality.Percolation.VertexRewardSpectralSplit
import Universality.Probability.PerronL2Sum

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

theorem ConfigurationHistory.weightedPopulation_add (rule : Rule) (state : LiveState)
    (first second : LiveState → ℝ) (n : ℕ) (history : rule.ConfigurationHistory n) :
    weightedPopulation rule state (first + second) n history =
      weightedPopulation rule state first n history + weightedPopulation rule state second n history := by
  unfold weightedPopulation
  simp only [FiniteNetwork.liveResponse_eq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem Classical.vertex_mass_perron_approximation {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (perron remainder : LiveState → ℝ) (eigenvalue : ℝ)
    (hsplit : rule.network.conditionalVertexMass p = perron + remainder)
    (hperron : rule.network.massMatrix p *ᵥ perron =
      (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal • perron)
    (hremainder : rule.network.massMatrix p *ᵥ remainder = eigenvalue • remainder)
    (hgap : |eigenvalue| < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal)
    (state : LiveState) :
    Tendsto (fun n : ℕ => eLpNorm (fun path =>
      (ConfigurationHistory.vertexMass rule state n path -
        ConfigurationHistory.weightedPopulation rule state perron n (path n) /
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal - 1)) /
        ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n)
      2 (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected))) atTop (𝓝 0) := by
  let probability := ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  let population (values : LiveState → ℝ) (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
    ConfigurationHistory.weightedPopulation rule state values n (path n)
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hpopMem (values : LiveState → ℝ) (n : ℕ) : MemLp (population values n) 2 probability :=
    ConfigurationHistory.memLp_infiniteLaw_observable rule p hp hp' hfixed (state == .connected) n
      (ConfigurationHistory.weightedPopulation rule state values n) 2
  have hsumMem (values : LiveState → ℝ) (n : ℕ) :
      MemLp (fun path => ∑ k ∈ Finset.range n, population values k path) 2 probability :=
    memLp_finsetSum _ (fun k _ => hpopMem values k)
  have hmassMem (n : ℕ) : MemLp (ConfigurationHistory.vertexMass rule state n) 2 probability :=
    ConfigurationHistory.memLp_vertexMass rule p hp hp' hfixed state n 2
  let rewardNoise (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
    (ConfigurationHistory.vertexMass rule state n path - ConfigurationHistory.vertexMass rule state 0 path -
      ∑ k ∈ Finset.range n, population (rule.network.conditionalVertexMass p) k path) / radius ^ n
  let initial (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
    ConfigurationHistory.vertexMass rule state 0 path / radius ^ n
  let otherSum (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
    (∑ k ∈ Finset.range n, population remainder k path) / radius ^ n
  let perronError (n : ℕ) (path : Π k, rule.ConfigurationHistory k) :=
    ((∑ k ∈ Finset.range n, population perron k path) - population perron n path / (radius - 1)) / radius ^ n
  have hfirstMeas (n : ℕ) : AEStronglyMeasurable (rewardNoise n) probability :=
    (memLp_div_const_real (((hmassMem n).sub (hmassMem 0)).sub (hsumMem _ n)) _).aestronglyMeasurable
  have hsecondMeas (n : ℕ) : AEStronglyMeasurable (initial n) probability :=
    (memLp_div_const_real (hmassMem 0) _).aestronglyMeasurable
  have hthirdMeas (n : ℕ) : AEStronglyMeasurable (otherSum n) probability :=
    (memLp_div_const_real (hsumMem remainder n) _).aestronglyMeasurable
  have hfourthMeas (n : ℕ) : AEStronglyMeasurable (perronError n) probability :=
    (memLp_div_const_real ((hsumMem perron n).sub (memLp_div_const_real (hpopMem perron n) _)) _).aestronglyMeasurable
  have hfirst : Tendsto (fun n => eLpNorm (rewardNoise n) 2 probability) atTop (𝓝 0) :=
    h.vertex_reward_compensation_L2_zero p hp hp' hfixed state
  have hsecond : Tendsto (fun n => eLpNorm (initial n) 2 probability) atTop (𝓝 0) :=
    L2_fixed_div_pow_zero _ (hmassMem 0) radius hradius
  have hthird : Tendsto (fun n => eLpNorm (otherSum n) 2 probability) atTop (𝓝 0) :=
    h.subcritical_population_sum_L2_zero p hp hp' hfixed remainder eigenvalue hremainder hgap state
  obtain ⟨bound, hbound, hnoise⟩ := h.eigenpopulation_innovation_bound p hp hp' hfixed perron radius hperron
  have hfourth : Tendsto (fun n => eLpNorm (perronError n) 2 probability) atTop (𝓝 0) :=
    perron_L2_sum_remainder_zero (μ := probability) (population perron) (hpopMem perron)
      bound radius hbound.le hradius (fun n => hnoise n state)
  have hcombined := L2_zero_add (μ := probability) _ _
    (fun n => ((hfirstMeas n).add (hsecondMeas n)).add (hthirdMeas n)) hfourthMeas
    (L2_zero_add (μ := probability) _ _ (fun n => (hfirstMeas n).add (hsecondMeas n)) hthirdMeas
      (L2_zero_add (μ := probability) _ _ hfirstMeas hsecondMeas hfirst hsecond) hthird) hfourth
  have heq (n : ℕ) : ((rewardNoise n + initial n) + otherSum n) + perronError n =
      (fun path => (ConfigurationHistory.vertexMass rule state n path -
        population perron n path / (radius - 1)) / radius ^ n) := by
    funext path
    change rewardNoise n path + initial n path + otherSum n path + perronError n path = _
    dsimp [rewardNoise, initial, otherSum, perronError]
    have hsplitpop (k : ℕ) : population (rule.network.conditionalVertexMass p) k path =
        population perron k path + population remainder k path := by
      rw [hsplit]
      exact ConfigurationHistory.weightedPopulation_add rule state perron remainder k (path k)
    simp_rw [hsplitpop, Finset.sum_add_distrib]
    ring
  exact hcombined.congr' (Eventually.of_forall (fun n =>
    congrArg (fun g : (Π k, rule.ConfigurationHistory k) → ℝ => eLpNorm g 2 probability) (heq n)))

end
end Universality.Rule
