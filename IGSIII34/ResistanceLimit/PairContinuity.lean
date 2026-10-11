import IGSIII34.ResistanceLimit.PairReindex
import IGSIII34.Resistance.Continuity
import IGSIII34.Percolation.NetworkEquivalence

set_option autoImplicit false
namespace IGSIII34.ResistanceLimit
noncomputable section
open Resistance Resistance.FiniteNetwork Filter
open scoped Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [Fintype Edge] [DecidableEq Edge]

theorem pairResistance_continuousOn_nonnegative
    (network : Resistance.FiniteNetwork Vertex Edge) (first last : Vertex) :
    ContinuousOn (fun resistance : Edge → ℝ => pairResistance network resistance first last)
      {resistance | ∀ edge, 0 ≤ resistance edge} := by
  by_cases distinct : first ≠ last
  · by_cases reachable : network.graph.Reachable first last
    · simpa only [pairResistance, dif_pos distinct] using
        (retarget network first last distinct).effectiveResistance_continuousOn_nonnegative reachable
    · simpa only [pairResistance_eq_zero_of_unreachable network _ reachable] using
        (continuousOn_const : ContinuousOn (fun _ : Edge → ℝ => (0 : ℝ)) {resistance | ∀ edge, 0 ≤ resistance edge})
  · have equal := not_ne_iff.mp distinct
    subst last
    simpa only [pairResistance_self] using
      (continuousOn_const : ContinuousOn (fun _ : Edge → ℝ => (0 : ℝ)) {resistance | ∀ edge, 0 ≤ resistance edge})

theorem pairResistance_scale
    (network : Resistance.FiniteNetwork Vertex Edge) (resistance : Edge → ℝ)
    (nonnegative : ∀ edge, 0 ≤ resistance edge) (scalar : ℝ) (scalarNonnegative : 0 ≤ scalar)
    (first last : Vertex) :
    pairResistance network (fun edge => scalar * resistance edge) first last =
      scalar * pairResistance network resistance first last := by
  by_cases distinct : first ≠ last
  · by_cases reachable : network.graph.Reachable first last
    · simp only [pairResistance, dif_pos distinct]
      exact (retarget network first last distinct).effectiveResistance_scale
        ((retarget network first last distinct).unitFlows_nonempty_of_connected reachable)
        nonnegative scalarNonnegative
    · rw [pairResistance_eq_zero_of_unreachable network _ reachable,
        pairResistance_eq_zero_of_unreachable network _ reachable, mul_zero]
  · have equal := not_ne_iff.mp distinct
    subst last
    rw [pairResistance_self, pairResistance_self, mul_zero]

theorem pairResistance_tendsto
    {Index : Type*} {filter : Filter Index}
    (network : Resistance.FiniteNetwork Vertex Edge)
    (resistance : Index → Edge → ℝ) (limit : Edge → ℝ)
    (nonnegative : ∀ index edge, 0 ≤ resistance index edge)
    (limitNonnegative : ∀ edge, 0 ≤ limit edge)
    (convergence : ∀ edge, Tendsto (fun index => resistance index edge) filter (𝓝 (limit edge)))
    (first last : Vertex) :
    Tendsto (fun index => pairResistance network (resistance index) first last) filter
      (𝓝 (pairResistance network limit first last)) := by
  have continuity : Tendsto (fun weights : Edge → ℝ => pairResistance network weights first last)
      (𝓝[{weights | ∀ edge, 0 ≤ weights edge}] limit)
      (𝓝 (pairResistance network limit first last)) :=
    pairResistance_continuousOn_nonnegative network first last limit limitNonnegative
  have values : Tendsto resistance filter (𝓝[{weights | ∀ edge, 0 ≤ weights edge}] limit) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_pi_nhds.mpr convergence,
      Eventually.of_forall (fun index => show resistance index ∈ {weights | ∀ edge, 0 ≤ weights edge} from nonnegative index)⟩
  simpa only [Function.comp_def] using continuity.comp values

theorem networkEquivalence_pairResistance
    {firstVertices firstEdges secondVertices secondEdges : ℕ}
    {first : Universality.FiniteNetwork firstVertices firstEdges}
    {second : Universality.FiniteNetwork secondVertices secondEdges}
    (equivalence : first.NetworkEquivalence second)
    (configuration : Universality.FiniteNetwork.Configuration firstEdges)
    (initial terminal : Fin firstVertices) :
    pairResistance (IGSIII34.Percolation.network second (equivalence.configuration configuration)) (fun _ => 1)
      (equivalence.vertex initial) (equivalence.vertex terminal) =
      pairResistance (IGSIII34.Percolation.network first configuration) (fun _ => 1) initial terminal := by
  exact pairResistance_reindex (IGSIII34.Percolation.network first configuration)
    (IGSIII34.Percolation.network second (equivalence.configuration configuration)) equivalence.vertex
    (IGSIII34.Percolation.networkEquivalenceOpenEdges equivalence configuration)
    (fun edge => equivalence.endpoint edge.val) (fun _ => 1) (fun _ => zero_lt_one) initial terminal

end
end IGSIII34.ResistanceLimit
