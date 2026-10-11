import Universality.Percolation.PhysicalClusterNumber
namespace Universality
noncomputable section
open Filter
open scoped Topology

theorem two_sided_raw_alpha_of_eventuallyEq (physical analytic : ℝ → ℝ)
    (critical exponent : ℝ) (heq : physical =ᶠ[𝓝 critical] analytic)
    (hresponse :
      ((∀ᶠ p in 𝓝[<] critical, iteratedDeriv 3 analytic p ≠ 0) ∧
        Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 analytic p| / Real.log |p - critical|)
          (𝓝[<] critical) (𝓝 exponent)) ∧
      ((∀ᶠ p in 𝓝[>] critical, iteratedDeriv 3 analytic p ≠ 0) ∧
        Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 analytic p| / Real.log |p - critical|)
          (𝓝[>] critical) (𝓝 exponent))) :
      ((∀ᶠ p in 𝓝[<] critical, iteratedDeriv 3 physical p ≠ 0) ∧
        Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 physical p| / Real.log |p - critical|)
          (𝓝[<] critical) (𝓝 exponent)) ∧
      ((∀ᶠ p in 𝓝[>] critical, iteratedDeriv 3 physical p ≠ 0) ∧
        Tendsto (fun p => -1 - Real.log |iteratedDeriv 3 physical p| / Real.log |p - critical|)
          (𝓝[>] critical) (𝓝 exponent)) := by
  have hleft := (heq.iteratedDeriv 3).filter_mono (nhdsWithin_le_nhds (s := Set.Iio critical))
  have hright := (heq.iteratedDeriv 3).filter_mono (nhdsWithin_le_nhds (s := Set.Ioi critical))
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · filter_upwards [hleft, hresponse.1.1] with p hp hnonzero
    simpa only [hp] using hnonzero
  · apply hresponse.1.2.congr'
    filter_upwards [hleft] with p hp
    rw [hp]
  · filter_upwards [hright, hresponse.2.1] with p hp hnonzero
    simpa only [hp] using hnonzero
  · apply hresponse.2.2.congr'
    filter_upwards [hright] with p hp
    rw [hp]

namespace Rule
variable [MeasurableSpace Bool] [MeasurableSingletonClass Bool]

theorem physicalClusterNumberDensity_iteratedDeriv_eq (rule : Rule)
    [Nonempty rule.network.InteriorVertex] [NeZero rule.edges]
    (hedges : 1 < rule.edges) (hvertices : 2 < rule.vertices)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (order : ℕ) :
    iteratedDeriv order (rule.physicalClusterNumberDensity hedges) p =
      iteratedDeriv order rule.network.clusterNumberAnalyticExtension p :=
  (rule.physicalClusterNumberDensity_eventually_eq hedges hvertices p hp hp').iteratedDeriv_eq order

end Rule
end
end Universality
