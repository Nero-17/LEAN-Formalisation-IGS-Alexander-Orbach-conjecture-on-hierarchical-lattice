import Universality.Graph.ClassicalSubstitution
import Universality.Graph.CrossingOpenCount
import Mathlib.Data.ZMod.Basic

/-!
# Terminal-exchange parity for actual two-edge graph configurations

The parity statement is obtained by pairing actual configurations under the
terminal-exchanging involution. No coefficient-parity premise is assumed.
-/

namespace Universality.Section4

theorem even_card_of_fixed_point_free_involution {α : Type*} [DecidableEq α]
    (set : Finset α) (involution : α → α)
    (hmem : ∀ value ∈ set, involution value ∈ set)
    (hinvolution : ∀ value ∈ set, involution (involution value) = value)
    (hfixed : ∀ value ∈ set, involution value ≠ value) : Even set.card := by
  have hsum : (∑ _ ∈ set, (1 : ZMod 2)) = 0 := by
    apply Finset.sum_involution (fun value _ => involution value)
    · intro value hvalue
      decide
    · intro value hvalue _
      exact hfixed value hvalue
    · exact hmem
    · exact hinvolution
  exact ZMod.natCast_eq_zero_iff_even.mp (by simpa using hsum)

theorem exists_fixed_point_of_not_even_card {α : Type*} [DecidableEq α]
    (set : Finset α) (involution : α → α)
    (hmem : ∀ value ∈ set, involution value ∈ set)
    (hinvolution : ∀ value ∈ set, involution (involution value) = value)
    (hcard : ¬ Even set.card) : ∃ value ∈ set, involution value = value := by
  by_contra hnone
  push Not at hnone
  exact hcard (even_card_of_fixed_point_free_involution set involution hmem hinvolution hnone)

end Universality.Section4

namespace Universality.FiniteNetwork
noncomputable section

variable {vertices edges : ℕ} (network : FiniteNetwork vertices edges)

theorem NetworkSymmetry.configuration_involutive (symmetry : network.NetworkSymmetry)
    (hedge : Function.Involutive symmetry.edge) :
    Function.Involutive symmetry.configurationEquiv := by
  have hinverse (edge : Fin edges) : symmetry.edge.symm edge = symmetry.edge edge := by
    apply symmetry.edge.injective
    rw [Equiv.apply_symm_apply, hedge]
  intro configuration
  funext edge
  simp only [NetworkSymmetry.configuration_apply, hinverse]
  exact congrArg configuration (hedge edge)

theorem NetworkSymmetry.openCount_configuration (symmetry : network.NetworkSymmetry)
    (configuration : Configuration edges) :
    openCount (symmetry.configurationEquiv configuration) = openCount configuration := by
  unfold openCount
  apply Finset.card_equiv symmetry.edge.symm
  intro edge
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    NetworkSymmetry.configuration_apply]

theorem NetworkSymmetry.complement_configuration (symmetry : network.NetworkSymmetry)
    (configuration : Configuration edges) :
    (fun edge => !(symmetry.configurationEquiv configuration edge)) =
      symmetry.configurationEquiv (fun edge => !(configuration edge)) := rfl

/-- In a connected graph, every vertex of an inclusion-minimal terminal cut
configuration is connected to one of the terminals. This derives the relevant
two-component fact directly from actual reachability and edge opening. -/
theorem minimal_cut_reachable_from_terminal (configuration : Configuration edges)
    (hconnected : ∀ vertex, network.fullGraph.Reachable network.source vertex)
    (hdisconnected : network.crosses configuration = false)
    (hminimal : ∀ edge, configuration edge = false →
      network.crosses (Function.update configuration edge true) = true)
    (vertex : Fin vertices) :
    (network.openGraph configuration).Reachable network.source vertex ∨
      (network.openGraph configuration).Reachable network.target vertex := by
  have hendpoints (edge : Fin edges) (hclosed : configuration edge = false) :
      ((network.openGraph configuration).Reachable network.source (network.endpoint edge).1 ∧
        (network.openGraph configuration).Reachable network.target (network.endpoint edge).2) ∨
      ((network.openGraph configuration).Reachable network.source (network.endpoint edge).2 ∧
        (network.openGraph configuration).Reachable network.target (network.endpoint edge).1) := by
    apply (network.pivotal_of_disconnected_iff configuration edge hdisconnected).mp
    have hupdate : Function.update configuration edge false = configuration := by
      simpa only [hclosed] using Function.update_eq_self edge configuration
    simp only [pivotal, hminimal edge hclosed, hupdate, hdisconnected,
      Bool.not_false, Bool.and_true]
  have hpropagate {first second : Fin vertices} (hadj : network.fullGraph.Adj first second)
      (hfirst : (network.openGraph configuration).Reachable network.source first ∨
        (network.openGraph configuration).Reachable network.target first) :
      (network.openGraph configuration).Reachable network.source second ∨
        (network.openGraph configuration).Reachable network.target second := by
    obtain ⟨hne, edge, _, hpair⟩ := hadj
    cases hopen : configuration edge
    · obtain hendpoint | hendpoint := hendpoints edge hopen
      · rcases hpair with hpair | hpair
        · exact Or.inr (by simpa only [hpair] using hendpoint.2)
        · exact Or.inl (by simpa only [hpair] using hendpoint.1)
      · rcases hpair with hpair | hpair
        · exact Or.inl (by simpa only [hpair] using hendpoint.1)
        · exact Or.inr (by simpa only [hpair] using hendpoint.2)
    · have hadjOpen : (network.openGraph configuration).Adj first second :=
        ⟨hne, edge, hopen, hpair⟩
      exact hfirst.elim (fun h => Or.inl (h.trans hadjOpen.reachable))
        (fun h => Or.inr (h.trans hadjOpen.reachable))
  have hwalk {first second : Fin vertices} (walk : network.fullGraph.Walk first second) :
      ((network.openGraph configuration).Reachable network.source first ∨
        (network.openGraph configuration).Reachable network.target first) →
      ((network.openGraph configuration).Reachable network.source second ∨
        (network.openGraph configuration).Reachable network.target second) := by
    induction walk with
    | nil => exact id
    | cons hadj walk ih => exact fun h => ih (hpropagate hadj h)
  obtain ⟨walk⟩ := hconnected vertex
  exact hwalk walk (Or.inl (.refl _))

theorem invariant_minimal_cut_has_no_fixed_vertex
    (symmetry : network.NetworkSymmetry)
    (hsource : symmetry.vertex network.source = network.target)
    (htarget : symmetry.vertex network.target = network.source)
    (configuration : Configuration edges)
    (hinvariant : symmetry.configurationEquiv configuration = configuration)
    (hconnected : ∀ vertex, network.fullGraph.Reachable network.source vertex)
    (hdisconnected : network.crosses configuration = false)
    (hminimal : ∀ edge, configuration edge = false →
      network.crosses (Function.update configuration edge true) = true)
    (vertex : Fin vertices) : symmetry.vertex vertex ≠ vertex := by
  intro hfixed
  have hnot : ¬ (network.openGraph configuration).Reachable network.source network.target := by
    intro hreach
    have hcross := (network.crosses_eq_true configuration).mpr hreach
    rw [hdisconnected] at hcross
    contradiction
  obtain hreach | hreach := network.minimal_cut_reachable_from_terminal configuration
    hconnected hdisconnected hminimal vertex
  · have hmapped := (symmetry.reachable_configuration_iff configuration network.source vertex).mpr hreach
    rw [hinvariant, hsource, hfixed] at hmapped
    exact hnot (hreach.trans hmapped.symm)
  · have hmapped := (symmetry.reachable_configuration_iff configuration network.target vertex).mpr hreach
    rw [hinvariant, htarget, hfixed] at hmapped
    exact hnot (hmapped.trans hreach.symm)

theorem update_true_eq_onlyClosed_of_closed_pair (configuration : Configuration edges)
    (first second : Fin edges) (hne : first ≠ second)
    (hclosed : (Finset.univ.filter fun edge => configuration edge = false) = {first, second}) :
    Function.update configuration first true = onlyClosed second := by
  funext edge
  by_cases hfirst : edge = first
  · subst edge
    simp [onlyClosed, hne]
  · rw [Function.update_of_ne hfirst]
    by_cases hsecond : edge = second
    · subst edge
      have hmem : second ∈ Finset.univ.filter (fun edge => configuration edge = false) := by
        rw [hclosed]
        simp
      have hvalue := (Finset.mem_filter.mp hmem).2
      simp [onlyClosed, hvalue]
    · have hvalue : configuration edge = true := by
        cases hvalue : configuration edge
        · have hmem : edge ∈ Finset.univ.filter (fun edge => configuration edge = false) :=
            Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalue⟩
          rw [hclosed] at hmem
          simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
          exact False.elim (hmem.elim hfirst hsecond)
        · rfl
      simp [onlyClosed, hsecond, hvalue]

theorem two_closed_cut_minimal (configuration : Configuration edges)
    (hcut : ∀ edge, network.crosses (onlyClosed edge) = true)
    (hcount : openCount (fun edge => !(configuration edge)) = 2) :
    ∀ edge, configuration edge = false →
      network.crosses (Function.update configuration edge true) = true := by
  have hcard : (Finset.univ.filter fun edge => configuration edge = false).card = 2 := by
    simpa only [openCount, Bool.not_eq_true_eq_eq_false] using hcount
  obtain ⟨first, second, hne, hclosed⟩ := Finset.card_eq_two.mp hcard
  intro edge hvalue
  have hmem : edge ∈ Finset.univ.filter (fun edge => configuration edge = false) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvalue⟩
  rw [hclosed] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with hfirst | hsecond
  · subst edge
    rw [update_true_eq_onlyClosed_of_closed_pair configuration first second hne hclosed]
    exact hcut second
  · subst edge
    rw [update_true_eq_onlyClosed_of_closed_pair configuration second first hne.symm
      (by simpa only [Finset.pair_comm] using hclosed)]
    exact hcut first

/-- In a two-open-edge configuration containing a length-two terminal path,
the source has just the path's middle vertex as a neighbor. -/
theorem two_open_source_neighbor_unique (configuration : Configuration edges)
    (hcount : openCount configuration = 2) (middle other : Fin vertices)
    (hfirst : (network.openGraph configuration).Adj network.source middle)
    (hsecond : (network.openGraph configuration).Adj middle network.target)
    (hother : (network.openGraph configuration).Adj network.source other) : other = middle := by
  have hdistinct : s(network.source, middle) ≠ s(middle, network.target) := by
    intro hequal
    rcases Sym2.eq_iff.mp hequal with ⟨hsource, _⟩ | ⟨hsource, _⟩
    · exact hfirst.ne hsource
    · exact network.terminals_distinct hsource
  have hsubset : {s(network.source, middle), s(middle, network.target)} ⊆
      (network.openGraph configuration).edgeFinset := by
    intro pair hpair
    simp only [Finset.mem_insert, Finset.mem_singleton] at hpair
    rcases hpair with rfl | rfl
    · exact SimpleGraph.mem_edgeFinset.mpr hfirst
    · exact SimpleGraph.mem_edgeFinset.mpr hsecond
  have hcard : (network.openGraph configuration).edgeFinset.card ≤ 2 := by
    rw [network.openGraph_edgeFinset]
    exact Finset.card_image_le.trans_eq hcount
  have hedges : {s(network.source, middle), s(middle, network.target)} =
      (network.openGraph configuration).edgeFinset := by
    apply Finset.eq_of_subset_of_card_le hsubset
    simpa [hdistinct] using hcard
  have hmember : s(network.source, other) ∈ (network.openGraph configuration).edgeFinset :=
    SimpleGraph.mem_edgeFinset.mpr hother
  rw [← hedges] at hmember
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmember
  rcases hmember with hequal | hequal
  · rcases Sym2.eq_iff.mp hequal with ⟨_, hother⟩ | ⟨hsource, _⟩
    · exact hother
    · exact False.elim (hfirst.ne hsource)
  · rcases Sym2.eq_iff.mp hequal with ⟨hsource, _⟩ | ⟨hsource, _⟩
    · exact False.elim (hfirst.ne hsource)
    · exact False.elim (network.terminals_distinct hsource)

/-- An invariant two-open-edge crossing has a fixed middle vertex under a
terminal-exchanging symmetry. -/
theorem invariant_two_open_crossing_has_fixed_vertex
    (symmetry : network.NetworkSymmetry)
    (htarget : symmetry.vertex network.target = network.source)
    (configuration : Configuration edges)
    (hinvariant : symmetry.configurationEquiv configuration = configuration)
    (hcross : network.crosses configuration = true)
    (hcount : openCount configuration = 2)
    (hscale : 1 < network.fullGraph.dist network.source network.target) :
    ∃ vertex, symmetry.vertex vertex = vertex := by
  have hreach := (network.crosses_eq_true configuration).mp hcross
  obtain ⟨walk, hpath, hlength⟩ := hreach.exists_path_of_dist
  have hlengthLe : walk.length ≤ 2 := by
    calc
      _ ≤ (network.openGraph configuration).edgeFinset.card :=
        hpath.isTrail.length_le_card_edgeFinset
      _ ≤ openCount configuration := by
        rw [network.openGraph_edgeFinset]
        exact Finset.card_image_le
      _ = 2 := hcount
  have hfullLe : network.fullGraph.dist network.source network.target ≤ walk.length := by
    rw [hlength]
    apply hreach.dist_anti
    intro first second hadj
    obtain ⟨hne, edge, _, hpair⟩ := hadj
    exact ⟨hne, edge, rfl, hpair⟩
  have hlengthTwo : walk.length = 2 := by omega
  obtain ⟨middle, hfirst, hsecond⟩ :=
    (network.openGraph configuration).walkLengthTwoEquivCommonNeighbors
      network.source network.target ⟨walk, hlengthTwo⟩
  refine ⟨middle, ?_⟩
  have hmapped := (symmetry.openGraphHom configuration).map_rel' hsecond
  change (network.openGraph (symmetry.configurationEquiv configuration)).Adj
    (symmetry.vertex network.target) (symmetry.vertex middle) at hmapped
  have hneighbor : (network.openGraph configuration).Adj network.source (symmetry.vertex middle) := by
    simpa only [hinvariant, htarget] using hmapped
  exact network.two_open_source_neighbor_unique configuration hcount middle _
    hfirst hsecond.symm hneighbor

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- The two-open crossing count and the two-closed failure count cannot both
be odd for an actual classical terminal-symmetric graph. -/
theorem Classical.two_edge_configuration_parity {rule : Rule} (h : rule.Classical) :
    Even (rule.network.crossingCountBySize 2) ∨
      Even ((Finset.univ.filter (fun configuration : Configuration rule.edges =>
        rule.network.crosses configuration = false ∧
          openCount (fun edge => !(configuration edge)) = 2)).card) := by
  classical
  by_cases hcrossEven : Even (rule.network.crossingCountBySize 2)
  · exact Or.inl hcrossEven
  right
  obtain ⟨symmetry, hinvolution, hsource⟩ := h.symmetric
  have htarget : symmetry.vertex rule.network.target = rule.network.source := by
    rw [← hsource]
    exact hinvolution _
  have hedge := symmetry.edge_involutive h.simple hinvolution
  have hconfigurationInvolutive :=
    NetworkSymmetry.configuration_involutive rule.network symmetry hedge
  have hcrossMem : ∀ configuration ∈ (Finset.univ.filter
      (fun configuration : Configuration rule.edges => rule.network.crosses configuration = true ∧
        openCount configuration = 2)), symmetry.configurationEquiv configuration ∈
      (Finset.univ.filter (fun configuration : Configuration rule.edges =>
        rule.network.crosses configuration = true ∧ openCount configuration = 2)) := by
    intro configuration hconfiguration
    obtain ⟨_, hcross, hcount⟩ := Finset.mem_filter.mp hconfiguration
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rwa [symmetry.crosses_configuration_of_terminal_swap hsource htarget]
    · rwa [NetworkSymmetry.openCount_configuration rule.network symmetry]
  obtain ⟨crossing, hcrossing, hcrossInvariant⟩ :=
    Section4.exists_fixed_point_of_not_even_card
      (Finset.univ.filter (fun configuration : Configuration rule.edges =>
        rule.network.crosses configuration = true ∧ openCount configuration = 2))
      symmetry.configurationEquiv hcrossMem (fun configuration _ => hconfigurationInvolutive configuration)
      hcrossEven
  obtain ⟨_, hcross, hcrossCount⟩ := Finset.mem_filter.mp hcrossing
  obtain ⟨fixedVertex, hfixedVertex⟩ :=
    rule.network.invariant_two_open_crossing_has_fixed_vertex symmetry htarget crossing
      hcrossInvariant hcross hcrossCount h.scale
  apply Section4.even_card_of_fixed_point_free_involution _ symmetry.configurationEquiv
  · intro configuration hconfiguration
    obtain ⟨_, hdisconnected, hcount⟩ := Finset.mem_filter.mp hconfiguration
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rwa [symmetry.crosses_configuration_of_terminal_swap hsource htarget]
    · rwa [NetworkSymmetry.complement_configuration rule.network symmetry,
        NetworkSymmetry.openCount_configuration rule.network symmetry]
  · intro configuration _
    exact hconfigurationInvolutive configuration
  · intro configuration hconfiguration hinvariant
    obtain ⟨_, hdisconnected, hcount⟩ := Finset.mem_filter.mp hconfiguration
    exact rule.network.invariant_minimal_cut_has_no_fixed_vertex symmetry hsource htarget
      configuration hinvariant h.connected hdisconnected
      (rule.network.two_closed_cut_minimal configuration h.cut hcount) fixedVertex hfixedVertex

end
end Universality.Rule

#print axioms Universality.FiniteNetwork.invariant_minimal_cut_has_no_fixed_vertex
#print axioms Universality.FiniteNetwork.two_closed_cut_minimal
#print axioms Universality.FiniteNetwork.invariant_two_open_crossing_has_fixed_vertex
#print axioms Universality.Rule.Classical.two_edge_configuration_parity
