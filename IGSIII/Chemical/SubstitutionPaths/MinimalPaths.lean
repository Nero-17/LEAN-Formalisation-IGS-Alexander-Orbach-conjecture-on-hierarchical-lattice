import IGSIII.Chemical.SubstitutionPaths.ActualPathCounting

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII.Chemical.Substitution

open Universality Universality.FiniteNetwork

noncomputable def configurationOfPath {edges : ℕ} (path : Finset (Fin edges)) : Configuration edges :=
  fun edge => decide (edge ∈ path)

theorem openEdges_configurationOfPath {edges : ℕ} (path : Finset (Fin edges)) :
    openEdges (configurationOfPath path) = path := by
  classical
  ext edge
  simp [openEdges, configurationOfPath]

theorem configurationOfPath_openEdges {edges : ℕ} (configuration : Configuration edges) :
    configurationOfPath (openEdges configuration) = configuration := by
  classical
  funext edge
  simp only [configurationOfPath, openEdges, Finset.mem_filter, Finset.mem_univ, true_and]
  cases configuration edge <;> rfl

theorem minimal_openEdges_mem {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (minimal : MinimalCrossingConfiguration network configuration) :
    openEdges configuration ∈ (edgePathFamily network configuration).paths := by
  classical
  obtain ⟨path, membership⟩ := (edgePathFamily network configuration).nonempty
  have equality : openEdges configuration = path := by
    ext edge
    constructor
    · intro retained
      have pivotal := minimal.2 edge ((Finset.mem_filter.mp retained).2)
      have common : edge ∈ (edgePathFamily network configuration).commonEdges := by
        rw [edgePathFamily_commonEdges_eq_pivotal network simple configuration minimal.1]
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, pivotal⟩
      exact (Finset.mem_filter.mp common).2 path membership
    · intro member
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, edgePathFamily_used_edge network simple configuration membership member⟩
  rwa [equality]

theorem edgePathFamily_member_minimal {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    {path : Finset (Fin edges)} (membership : path ∈ (edgePathFamily network configuration).paths) :
    MinimalCrossingConfiguration network (configurationOfPath path) := by
  classical
  have reachable := (network.crosses_eq_true _).mp crossing
  simp only [edgePathFamily, dif_pos reachable] at membership
  obtain ⟨bondPath, bondMembership, rfl⟩ := Finset.mem_image.mp membership
  have fullMembership : bondPath ∈ graphPathSets network.fullGraph network.source network.target := by
    obtain ⟨walk, simpleWalk, rfl⟩ := (mem_graphPathFamily _ _ _ reachable bondPath).mp bondMembership
    exact (mem_graphPathSets _ _ _ _).mpr
      ⟨walk.mapLe (network.openGraph_le_full configuration), simpleWalk.mapLe _, by simp⟩
  have equality : configurationOfPath (indexedPath network bondPath) = pathEdgeConfiguration network bondPath := by
    funext edge
    simp [configurationOfPath, indexedPath, pathEdgeConfiguration]
  rw [equality]
  exact pathEdgeConfiguration_minimal network simple bondPath fullMembership

theorem edgePathFamily_mem_iff_minimal {vertices edges : ℕ} (network : FiniteNetwork vertices edges)
    (simple : Function.Injective (fun edge => s((network.endpoint edge).1, (network.endpoint edge).2)))
    (configuration : Configuration edges) (crossing : network.crosses configuration = true)
    (path : Finset (Fin edges)) :
    path ∈ (edgePathFamily network configuration).paths ↔
      MinimalCrossingConfiguration network (configurationOfPath path) ∧
        ∀ edge ∈ path, configuration edge = true := by
  constructor
  · intro membership
    exact ⟨edgePathFamily_member_minimal network simple configuration crossing membership,
      fun _ retained => edgePathFamily_used_edge network simple configuration membership retained⟩
  · rintro ⟨minimal, retained⟩
    have own := minimal_openEdges_mem network simple (configurationOfPath path) minimal
    rw [openEdges_configurationOfPath] at own
    exact edgePathFamily_mono network (configurationOfPath path) configuration
      (fun edge opened => retained edge (of_decide_eq_true opened)) minimal.1 own

theorem minimal_substitute_of_children
    {outerVertices outerEdges innerVertices innerEdges : ℕ}
    (outer : FiniteNetwork outerVertices outerEdges) (inner : FiniteNetwork innerVertices innerEdges)
    (cells : Fin outerEdges → Configuration innerEdges)
    (coarseMinimal : MinimalCrossingConfiguration outer (inner.coarseConfiguration cells))
    (childrenMinimal : ∀ edge, (∃ child, cells edge child = true) → MinimalCrossingConfiguration inner (cells edge)) :
    MinimalCrossingConfiguration (outer.substitute inner) (substitutionConfigurationEquiv cells) := by
  refine ⟨by simpa only [outer.substitute_crosses inner] using coarseMinimal.1, ?_⟩
  intro leaf retained
  obtain ⟨⟨edge, child⟩, rfl⟩ := finProdFinEquiv.surjective leaf
  have childRetained : cells edge child = true := by
    simpa only [substitutionConfigurationEquiv, Equiv.coe_fn_mk, Equiv.symm_apply_apply] using retained
  have minimal := childrenMinimal edge ⟨child, childRetained⟩
  rw [substitute_pivotal_factor, coarseMinimal.2 edge minimal.1, minimal.2 child childRetained]
  rfl

end IGSIII.Chemical.Substitution
