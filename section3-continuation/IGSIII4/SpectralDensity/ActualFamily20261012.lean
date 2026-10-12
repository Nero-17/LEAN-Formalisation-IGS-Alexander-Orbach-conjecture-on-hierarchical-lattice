import Universality.Graph.ClassicalRule
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

/-- Outer terminals and the short midpoint; chain junctions; internal path vertices. -/
abbrev Vertex (blocks paths interior : ℕ) :=
  Fin 3 ⊕ (Fin (blocks + 1) ⊕ (Fin blocks × Fin paths × Fin (interior + 1)))

/-- Two short-path edges, two exterior edges, and the edges of all block paths. -/
abbrev Edge (blocks paths interior : ℕ) :=
  Fin 4 ⊕ (Fin blocks × Fin paths × Fin (interior + 2))

def source (blocks paths interior : ℕ) : Vertex blocks paths interior := .inl 0
def midpoint (blocks paths interior : ℕ) : Vertex blocks paths interior := .inl 1
def target (blocks paths interior : ℕ) : Vertex blocks paths interior := .inl 2

def pathVertex (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (position : Fin (interior + 3)) : Vertex blocks paths interior :=
  if first : position.val = 0 then .inr (.inl block.castSucc)
  else if last : position.val = interior + 2 then .inr (.inl block.succ)
  else .inr (.inr (block, path, ⟨position.val - 1, by omega⟩))

def endpoint (blocks paths interior : ℕ) :
    Edge blocks paths interior → Vertex blocks paths interior × Vertex blocks paths interior
  | .inl edge =>
      if edge.val = 0 then (source blocks paths interior, midpoint blocks paths interior)
      else if edge.val = 1 then (midpoint blocks paths interior, target blocks paths interior)
      else if edge.val = 2 then (source blocks paths interior, .inr (.inl 0))
      else (.inr (.inl (Fin.last blocks)), target blocks paths interior)
  | .inr (block, path, edge) =>
      (pathVertex blocks paths interior block path edge.castSucc,
        pathVertex blocks paths interior block path edge.succ)

theorem pathVertex_injective (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths) :
    Function.Injective (pathVertex blocks paths interior block path) := by
  let recover : Vertex blocks paths interior → ℕ := fun vertex =>
    match vertex with
    | .inl _ => 0
    | .inr (.inl junction) => if junction = block.castSucc then 0 else interior + 2
    | .inr (.inr (_, _, position)) => position.val + 1
  have recovery (position : Fin (interior + 3)) :
      recover (pathVertex blocks paths interior block path position) = position.val := by
    have bound := position.isLt
    have different : block.succ ≠ block.castSucc := by
      intro equal
      have := congrArg Fin.val equal
      simp only [Fin.val_succ, Fin.val_castSucc] at this
      omega
    simp only [pathVertex]
    split_ifs with first last
    · simp [recover, first]
    · simp [recover, different, last]
    · simp only [recover]
      omega
  intro first second equal
  apply Fin.ext
  have recovered := congrArg recover equal
  simpa only [recovery] using recovered

theorem endpoint_loopless (blocks paths interior : ℕ) (edge : Edge blocks paths interior) :
    (endpoint blocks paths interior edge).1 ≠ (endpoint blocks paths interior edge).2 := by
  rcases edge with edge | ⟨block, path, edge⟩
  · fin_cases edge <;> simp [endpoint, source, midpoint, target]
  · intro equal
    change pathVertex blocks paths interior block path edge.castSucc =
      pathVertex blocks paths interior block path edge.succ at equal
    have same := pathVertex_injective blocks paths interior block path equal
    have := congrArg Fin.val same
    simp only [Fin.val_castSucc, Fin.val_succ] at this
    omega

/-- The finite indexed network actually used by the substitution model. -/
def network (blocks paths interior : ℕ) :
    FiniteNetwork (Fintype.card (Vertex blocks paths interior))
      (Fintype.card (Edge blocks paths interior)) where
  endpoint edge :=
    ((Fintype.equivFin (Vertex blocks paths interior))
      (endpoint blocks paths interior ((Fintype.equivFin (Edge blocks paths interior)).symm edge)).1,
     (Fintype.equivFin (Vertex blocks paths interior))
      (endpoint blocks paths interior ((Fintype.equivFin (Edge blocks paths interior)).symm edge)).2)
  source := Fintype.equivFin _ (source blocks paths interior)
  target := Fintype.equivFin _ (target blocks paths interior)
  terminals_distinct := by
    intro equal
    have := (Fintype.equivFin _).injective equal
    simp [source, target] at this
  loopless edge := fun equal => endpoint_loopless blocks paths interior _
    ((Fintype.equivFin _).injective equal)

abbrev rule (blocks paths interior : ℕ) : Rule :=
  ⟨_, _, network blocks paths interior⟩

theorem rule_edges (blocks paths interior : ℕ) :
    (rule blocks paths interior).edges = 4 + blocks * paths * (interior + 2) := by
  simp [rule, Edge, Fintype.card_sum, Fintype.card_prod, Nat.mul_assoc]

theorem rule_vertices (blocks paths interior : ℕ) :
    (rule blocks paths interior).vertices =
      3 + (blocks + 1) + blocks * paths * (interior + 1) := by
  simp [rule, Vertex, Fintype.card_sum, Fintype.card_prod, Nat.mul_assoc, Nat.add_assoc]

/-- A typed presentation of precisely the actual finite-network adjacency. -/
def graph (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool) :
    SimpleGraph (Vertex blocks paths interior) where
  Adj first second := first ≠ second ∧ ∃ edge, configuration edge = true ∧
    (endpoint blocks paths interior edge = (first, second) ∨
      endpoint blocks paths interior edge = (second, first))
  symm := ⟨by
    rintro first second ⟨distinct, edge, opened, forward | backward⟩
    · exact ⟨distinct.symm, edge, opened, Or.inr forward⟩
    · exact ⟨distinct.symm, edge, opened, Or.inl backward⟩⟩
  loopless := ⟨by intro vertex adjacent; exact adjacent.1 rfl⟩

theorem graph_edge (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool)
    (edge : Edge blocks paths interior) (opened : configuration edge = true) :
    (graph blocks paths interior configuration).Adj
      (endpoint blocks paths interior edge).1 (endpoint blocks paths interior edge).2 :=
  ⟨endpoint_loopless blocks paths interior edge, edge, opened, Or.inl rfl⟩

def graphIso (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool) :
    graph blocks paths interior configuration ≃g
      (network blocks paths interior).openGraph
        (fun edge => configuration ((Fintype.equivFin _).symm edge)) where
  toEquiv := Fintype.equivFin _
  map_rel_iff' := by
    intro first second
    constructor
    · rintro ⟨distinct, edge, opened, forward | backward⟩
      · refine ⟨fun equal => distinct (congrArg (Fintype.equivFin (Vertex blocks paths interior)) equal),
          (Fintype.equivFin _).symm edge, opened, Or.inl ?_⟩
        apply Prod.ext <;> apply (Fintype.equivFin _).injective
        · exact congrArg Prod.fst forward
        · exact congrArg Prod.snd forward
      · refine ⟨fun equal => distinct (congrArg (Fintype.equivFin (Vertex blocks paths interior)) equal),
          (Fintype.equivFin _).symm edge, opened, Or.inr ?_⟩
        apply Prod.ext <;> apply (Fintype.equivFin _).injective
        · exact congrArg Prod.fst backward
        · exact congrArg Prod.snd backward
    · rintro ⟨distinct, edge, opened, forward | backward⟩
      · refine ⟨fun equal => distinct ((Fintype.equivFin (Vertex blocks paths interior)).injective equal),
          Fintype.equivFin _ edge, ?_, Or.inl ?_⟩
        · simpa using opened
        · simp only [network, Equiv.symm_apply_apply]
          rw [forward]
      · refine ⟨fun equal => distinct ((Fintype.equivFin (Vertex blocks paths interior)).injective equal),
          Fintype.equivFin _ edge, ?_, Or.inr ?_⟩
        · simpa using opened
        · simp only [network, Equiv.symm_apply_apply]
          rw [backward]

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

variable (blocks paths interior : ℕ)

def shortWalk (configuration : Edge blocks paths interior → Bool)
    (firstOpen : configuration (.inl 0) = true)
    (secondOpen : configuration (.inl 1) = true) :
    (graph blocks paths interior configuration).Walk
      (source blocks paths interior) (target blocks paths interior) :=
  .cons (by simpa [endpoint] using graph_edge blocks paths interior configuration (.inl 0) firstOpen)
    (.cons (by simpa [endpoint] using graph_edge blocks paths interior configuration (.inl 1) secondOpen) .nil)

theorem path_reachable (configuration : Edge blocks paths interior → Bool)
    (block : Fin blocks) (path : Fin paths)
    (opened : ∀ edge, configuration (.inr (block, path, edge)) = true)
    (position : Fin (interior + 3)) :
    (graph blocks paths interior configuration).Reachable
      (pathVertex blocks paths interior block path 0)
      (pathVertex blocks paths interior block path position) := by
  induction position using Fin.induction with
  | zero => exact .refl _
  | succ position previous =>
    exact previous.trans
      (graph_edge blocks paths interior configuration (.inr (block, path, position))
        (opened position)).reachable

theorem chain_reachable (configuration : Edge blocks paths interior → Bool)
    (path : Fin paths)
    (opened : ∀ block edge, configuration (.inr (block, path, edge)) = true)
    (junction : Fin (blocks + 1)) :
    (graph blocks paths interior configuration).Reachable
      (.inr (.inl 0)) (.inr (.inl junction)) := by
  induction junction using Fin.induction with
  | zero => exact .refl _
  | succ junction previous =>
    apply previous.trans
    simpa [pathVertex] using
      path_reachable blocks paths interior configuration junction path (opened junction)
        (Fin.last (interior + 2))

theorem long_reachable (configuration : Edge blocks paths interior → Bool)
    (path : Fin paths)
    (opened : ∀ block edge, configuration (.inr (block, path, edge)) = true)
    (firstExterior : configuration (.inl 2) = true)
    (lastExterior : configuration (.inl 3) = true) :
    (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (target blocks paths interior) := by
  have first := (graph_edge blocks paths interior configuration (.inl 2) firstExterior).reachable
  have last := (graph_edge blocks paths interior configuration (.inl 3) lastExterior).reachable
  exact (show (graph blocks paths interior configuration).Reachable
    (source blocks paths interior) (.inr (.inl 0)) from by simpa [endpoint] using first).trans
    ((chain_reachable blocks paths interior configuration path opened (Fin.last blocks)).trans
      (by simpa [endpoint] using last))

theorem no_direct_edge :
    ¬ (graph blocks paths interior (fun _ => true)).Adj
      (source blocks paths interior) (target blocks paths interior) := by
  rintro ⟨_, edge, _, forward | backward⟩
  all_goals rcases edge with edge | ⟨block, path, edge⟩
  · fin_cases edge <;> simp [endpoint, source, midpoint, target] at forward
  · simp only [endpoint] at forward
    have := congrArg Prod.fst forward
    simp [pathVertex, source] at this
    split_ifs at this <;> simp_all
  · fin_cases edge <;> simp [endpoint, source, midpoint, target] at backward
  · simp only [endpoint] at backward
    have := congrArg Prod.fst backward
    simp [pathVertex, target] at this
    split_ifs at this <;> simp_all

theorem terminal_distance :
    (network blocks paths interior).fullGraph.dist
      (network blocks paths interior).source (network blocks paths interior).target = 2 := by
  let short := (shortWalk blocks paths interior (fun _ => true) rfl rfl).map
    (graphIso blocks paths interior (fun _ => true)).toHom
  have connected : (network blocks paths interior).fullGraph.Reachable
      (network blocks paths interior).source (network blocks paths interior).target := ⟨short⟩
  have notAdjacent : ¬ (network blocks paths interior).fullGraph.Adj
      (network blocks paths interior).source (network blocks paths interior).target := by
    intro adjacent
    exact no_direct_edge blocks paths interior
      ((graphIso blocks paths interior (fun _ => true)).map_rel_iff.mp adjacent)
  have lower := connected.one_lt_dist_of_ne_of_not_adj
    (network blocks paths interior).terminals_distinct notAdjacent
  have upper : (network blocks paths interior).fullGraph.dist
      (network blocks paths interior).source (network blocks paths interior).target ≤ short.length :=
    SimpleGraph.dist_le short
  have length : short.length = 2 := by simp [short, shortWalk]
  rw [length] at upper
  omega

theorem one_edge_deletion_survives (pathsPositive : 0 < paths)
    (removed : Fin (Fintype.card (Edge blocks paths interior))) :
    (network blocks paths interior).crosses (onlyClosed removed) = true := by
  let configuration : Edge blocks paths interior → Bool :=
    fun edge => if edge = (Fintype.equivFin _).symm removed then false else true
  have typedReachable : (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (target blocks paths interior) := by
    rcases equality : (Fintype.equivFin (Edge blocks paths interior)).symm removed with removedEdge | removedEdge
    · fin_cases removedEdge
      · apply long_reachable blocks paths interior configuration ⟨0, pathsPositive⟩
        all_goals try intros
        all_goals simp [configuration, equality]
      · apply long_reachable blocks paths interior configuration ⟨0, pathsPositive⟩
        all_goals try intros
        all_goals simp [configuration, equality]
      · exact ⟨shortWalk blocks paths interior configuration
          (by simp [configuration, equality])
          (by simp [configuration, equality])⟩
      · exact ⟨shortWalk blocks paths interior configuration
          (by simp [configuration, equality])
          (by simp [configuration, equality])⟩
    · exact ⟨shortWalk blocks paths interior configuration
        (by simp [configuration, equality])
        (by simp [configuration, equality])⟩
  apply ((network blocks paths interior).crosses_eq_true _).mpr
  have relabelled := typedReachable.map (graphIso blocks paths interior configuration).toHom
  have mappedConfiguration : (fun edge => configuration ((Fintype.equivFin _).symm edge)) =
      onlyClosed removed := by
    funext edge
    by_cases equal : edge = removed
    · subst edge
      simp [configuration, onlyClosed]
    · have different : (Fintype.equivFin (Edge blocks paths interior)).symm edge ≠
          (Fintype.equivFin (Edge blocks paths interior)).symm removed :=
        fun same => equal ((Fintype.equivFin _).symm.injective same)
      simp [configuration, different, onlyClosed, Function.update_of_ne equal]
  change ((network blocks paths interior).openGraph
    (fun edge => configuration ((Fintype.equivFin _).symm edge))).Reachable
    (network blocks paths interior).source (network blocks paths interior).target at relabelled
  rw [mappedConfiguration] at relabelled
  exact relabelled

theorem own_interior_fixed_point (pathsPositive : 0 < paths) :
    ∃ probability : ℝ, 0 < probability ∧ probability < 1 ∧
      (network blocks paths interior).reliability probability = probability := by
  apply (network blocks paths interior).exists_interior_fixed_point
  · exact ⟨(shortWalk blocks paths interior (fun _ => true) rfl rfl).map
      (graphIso blocks paths interior (fun _ => true)).toHom⟩
  · rw [terminal_distance]
    omega
  · exact one_edge_deletion_survives blocks paths interior pathsPositive

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

/-- Every vertex belongs to the same actual finite graph component. -/
theorem connected (blocks paths interior : ℕ) (pathsPositive : 0 < paths)
    (vertex : Vertex blocks paths interior) :
    (graph blocks paths interior (fun _ => true)).Reachable
      (source blocks paths interior) vertex := by
  have first := (graph_edge blocks paths interior (fun _ => true) (.inl 2) rfl).reachable
  have reachJunction (junction : Fin (blocks + 1)) :
      (graph blocks paths interior (fun _ => true)).Reachable
        (source blocks paths interior) (.inr (.inl junction)) := by
    apply (show (graph blocks paths interior (fun _ => true)).Reachable
      (source blocks paths interior) (.inr (.inl 0)) from by simpa [endpoint] using first).trans
    exact chain_reachable blocks paths interior (fun _ => true) ⟨0, pathsPositive⟩
      (fun _ _ => rfl) junction
  rcases vertex with vertex | vertex
  · fin_cases vertex
    · exact .refl _
    · exact (graph_edge blocks paths interior (fun _ => true) (.inl 0) rfl).reachable
    · exact ⟨shortWalk blocks paths interior (fun _ => true) rfl rfl⟩
  · rcases vertex with junction | ⟨block, path, position⟩
    · exact reachJunction junction
    · apply (reachJunction block.castSucc).trans
      have reach := path_reachable blocks paths interior (fun _ => true) block path
        (fun _ => rfl) ⟨position.val + 1, by omega⟩
      simpa [pathVertex, show position.val + 1 ≠ 0 by omega,
        show position.val + 1 ≠ interior + 2 by omega,
        show position.val ≠ interior + 1 by omega] using reach

theorem network_connected (blocks paths interior : ℕ) (pathsPositive : 0 < paths)
    (vertex : Fin (Fintype.card (Vertex blocks paths interior))) :
    (network blocks paths interior).fullGraph.Reachable
      (network blocks paths interior).source vertex := by
  have relabelled :=
    (connected blocks paths interior pathsPositive ((Fintype.equivFin _).symm vertex)).map
      (graphIso blocks paths interior (fun _ => true)).toHom
  change (network blocks paths interior).fullGraph.Reachable
    (network blocks paths interior).source
    ((Fintype.equivFin (Vertex blocks paths interior))
      ((Fintype.equivFin (Vertex blocks paths interior)).symm vertex)) at relabelled
  simpa only [Equiv.apply_symm_apply] using relabelled

end
end IGSIII4.SpectralDensity.ActualFamily


namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def height (blocks paths interior : ℕ) : Vertex blocks paths interior → ℕ
  | .inl vertex => if vertex.val = 0 then 0 else if vertex.val = 1 then 1
      else blocks * (interior + 2) + 2
  | .inr (.inl junction) => junction.val * (interior + 2) + 1
  | .inr (.inr (block, _, position)) => block.val * (interior + 2) + position.val + 2

theorem pathVertex_height (blocks paths interior : ℕ) (block : Fin blocks)
    (path : Fin paths) (position : Fin (interior + 3)) :
    height blocks paths interior (pathVertex blocks paths interior block path position) =
      block.val * (interior + 2) + position.val + 1 := by
  have bound := position.isLt
  simp only [pathVertex]
  split_ifs with first last
  · simp [height, first]
  · simp [height, last, Nat.add_mul]
  · simp only [height]
    omega

theorem endpoint_height_strict (blocks paths interior : ℕ) (edge : Edge blocks paths interior) :
    height blocks paths interior (endpoint blocks paths interior edge).1 <
      height blocks paths interior (endpoint blocks paths interior edge).2 := by
  rcases edge with edge | ⟨block, path, edge⟩
  · fin_cases edge <;> simp [endpoint, height, source, midpoint, target]
    all_goals omega
  · simp only [endpoint, pathVertex_height, Fin.val_castSucc, Fin.val_succ]
    omega

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

theorem endpoint_injective (blocks paths interior : ℕ) :
    Function.Injective (endpoint blocks paths interior) := by
  intro first second equal
  rcases first with first | ⟨firstBlock, firstPath, firstEdge⟩
  · rcases second with second | ⟨secondBlock, secondPath, secondEdge⟩
    · fin_cases first <;> fin_cases second <;>
        simp_all [endpoint, source, midpoint, target]
    · fin_cases first <;> simp only [endpoint] at equal
      all_goals simp only [pathVertex] at equal
      all_goals split_ifs at equal <;> simp_all [source, midpoint, target]
  · rcases second with second | ⟨secondBlock, secondPath, secondEdge⟩
    · fin_cases second <;> simp only [endpoint] at equal
      all_goals simp only [pathVertex] at equal
      all_goals split_ifs at equal <;> simp_all [source, midpoint, target]
    · have firstBound := firstEdge.isLt
      have secondBound := secondEdge.isLt
      simp only [endpoint, pathVertex, Fin.val_castSucc, Fin.val_succ] at equal
      split_ifs at equal <;>
        simp_all only [Prod.mk.injEq, Sum.inr.injEq, Sum.inl.injEq, Fin.ext_iff,
          Fin.val_castSucc, Fin.val_succ]
      all_goals simp_all
      all_goals omega

theorem simple (blocks paths interior : ℕ) :
    Function.Injective (fun edge =>
      s(((network blocks paths interior).endpoint edge).1,
        ((network blocks paths interior).endpoint edge).2)) := by
  intro first second equal
  rcases Sym2.eq_iff.mp equal with ⟨forwardFirst, forwardSecond⟩ | ⟨reverseFirst, reverseSecond⟩
  · apply (Fintype.equivFin (Edge blocks paths interior)).symm.injective
    apply endpoint_injective blocks paths interior
    apply Prod.ext
    · exact (Fintype.equivFin (Vertex blocks paths interior)).injective forwardFirst
    · exact (Fintype.equivFin (Vertex blocks paths interior)).injective forwardSecond
  · have firstStrict := endpoint_height_strict blocks paths interior
      ((Fintype.equivFin (Edge blocks paths interior)).symm first)
    have secondStrict := endpoint_height_strict blocks paths interior
      ((Fintype.equivFin (Edge blocks paths interior)).symm second)
    have firstEqual := (Fintype.equivFin (Vertex blocks paths interior)).injective reverseFirst
    have secondEqual := (Fintype.equivFin (Vertex blocks paths interior)).injective reverseSecond
    change (endpoint blocks paths interior ((Fintype.equivFin _).symm first)).1 =
      (endpoint blocks paths interior ((Fintype.equivFin _).symm second)).2 at firstEqual
    change (endpoint blocks paths interior ((Fintype.equivFin _).symm first)).2 =
      (endpoint blocks paths interior ((Fintype.equivFin _).symm second)).1 at secondEqual
    rw [firstEqual, secondEqual] at firstStrict
    omega

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def reflectVertex (blocks paths interior : ℕ) : Vertex blocks paths interior → Vertex blocks paths interior
  | .inl vertex => .inl vertex.rev
  | .inr (.inl junction) => .inr (.inl junction.rev)
  | .inr (.inr (block, path, position)) => .inr (.inr (block.rev, path, position.rev))

theorem reflectVertex_involutive (blocks paths interior : ℕ) :
    Function.Involutive (reflectVertex blocks paths interior) := by
  rintro (vertex | (junction | ⟨block, path, position⟩)) <;>
    simp [reflectVertex]

theorem reflect_pathVertex (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (position : Fin (interior + 3)) :
    reflectVertex blocks paths interior (pathVertex blocks paths interior block path position) =
      pathVertex blocks paths interior block.rev path position.rev := by
  have bound := position.isLt
  have blockBound := block.isLt
  simp only [pathVertex, Fin.val_rev]
  split_ifs <;> simp_all only [reflectVertex, Sum.inr.injEq, Sum.inl.injEq,
    Prod.mk.injEq, Fin.ext_iff, Fin.val_rev, Fin.val_castSucc, Fin.val_succ]
  all_goals try simp_all only [reduceCtorEq]
  all_goals try simp_all only [true_and, and_true]
  all_goals omega

def reflectEdge (blocks paths interior : ℕ) : Edge blocks paths interior → Edge blocks paths interior
  | .inl edge => .inl ⟨if edge.val = 0 then 1 else if edge.val = 1 then 0
      else if edge.val = 2 then 3 else 2, by split_ifs <;> omega⟩
  | .inr (block, path, edge) => .inr (block.rev, path, edge.rev)

theorem reflectEdge_involutive (blocks paths interior : ℕ) :
    Function.Involutive (reflectEdge blocks paths interior) := by
  rintro (edge | ⟨block, path, edge⟩)
  · fin_cases edge <;> simp [reflectEdge]
  · simp [reflectEdge]

theorem reflect_endpoint (blocks paths interior : ℕ) (edge : Edge blocks paths interior) :
    endpoint blocks paths interior (reflectEdge blocks paths interior edge) =
      (reflectVertex blocks paths interior (endpoint blocks paths interior edge).2,
        reflectVertex blocks paths interior (endpoint blocks paths interior edge).1) := by
  rcases edge with edge | ⟨block, path, edge⟩
  · fin_cases edge <;> simp [reflectEdge, endpoint, source, target, midpoint, reflectVertex]
  · simp only [reflectEdge, endpoint, reflect_pathVertex, Fin.rev_castSucc, Fin.rev_succ]

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def Forward (blocks paths interior : ℕ) (first second : Vertex blocks paths interior) : Prop :=
  ∃ edge, endpoint blocks paths interior edge = (first, second)

abbrev ForwardReachable (blocks paths interior : ℕ) :=
  Relation.ReflTransGen (Forward blocks paths interior)

theorem forward_path (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (position : Fin (interior + 3)) :
    ForwardReachable blocks paths interior (pathVertex blocks paths interior block path 0)
      (pathVertex blocks paths interior block path position) := by
  induction position using Fin.induction with
  | zero => exact .refl
  | succ position previous => exact previous.tail ⟨.inr (block, path, position), rfl⟩

theorem forward_chain (blocks paths interior : ℕ) (path : Fin paths)
    (junction : Fin (blocks + 1)) :
    ForwardReachable blocks paths interior (.inr (.inl 0)) (.inr (.inl junction)) := by
  induction junction using Fin.induction with
  | zero => exact .refl
  | succ junction previous =>
    apply previous.trans
    simpa [pathVertex] using forward_path blocks paths interior junction path (Fin.last (interior + 2))

theorem forward_connected (blocks paths interior : ℕ) (pathsPositive : 0 < paths)
    (vertex : Vertex blocks paths interior) :
    ForwardReachable blocks paths interior (source blocks paths interior) vertex := by
  have first : ForwardReachable blocks paths interior (source blocks paths interior) (.inr (.inl 0)) :=
    .single ⟨.inl 2, by simp [endpoint]⟩
  have reachJunction (junction : Fin (blocks + 1)) :
      ForwardReachable blocks paths interior (source blocks paths interior) (.inr (.inl junction)) :=
    first.trans (forward_chain blocks paths interior ⟨0, pathsPositive⟩ junction)
  rcases vertex with vertex | vertex
  · fin_cases vertex
    · exact .refl
    · exact .single ⟨.inl 0, by simp [endpoint, midpoint]⟩
    · exact (show ForwardReachable blocks paths interior (source blocks paths interior)
        (midpoint blocks paths interior) from .single ⟨.inl 0, by simp [endpoint]⟩).tail
          ⟨.inl 1, by simp [endpoint, target]⟩
  · rcases vertex with junction | ⟨block, path, position⟩
    · exact reachJunction junction
    · apply (reachJunction block.castSucc).trans
      have reach := forward_path blocks paths interior block path ⟨position.val + 1, by omega⟩
      simpa [pathVertex, show position.val + 1 ≠ 0 by omega,
        show position.val + 1 ≠ interior + 2 by omega,
        show position.val ≠ interior + 1 by omega] using reach

theorem forward_reflect (blocks paths interior : ℕ) {first second : Vertex blocks paths interior}
    (reach : ForwardReachable blocks paths interior first second) :
    ForwardReachable blocks paths interior (reflectVertex blocks paths interior second)
      (reflectVertex blocks paths interior first) := by
  induction reach with
  | refl => exact .refl
  | @tail middle last reach step previous =>
    obtain ⟨edge, equal⟩ := step
    apply (Relation.ReflTransGen.single ?_).trans previous
    refine ⟨reflectEdge blocks paths interior edge, ?_⟩
    rw [reflect_endpoint, equal]

def Increasing {blocks paths interior : ℕ} {first last : Vertex blocks paths interior} :
    (graph blocks paths interior (fun _ => true)).Walk first last → Prop
  | .nil => True
  | @SimpleGraph.Walk.cons _ _ first middle last _ rest =>
      height blocks paths interior first < height blocks paths interior middle ∧ Increasing rest

theorem increasing_concat {blocks paths interior : ℕ} {first middle last : Vertex blocks paths interior}
    (walk : (graph blocks paths interior (fun _ => true)).Walk first middle)
    (adjacent : (graph blocks paths interior (fun _ => true)).Adj middle last)
    (increasing : Increasing walk)
    (strict : height blocks paths interior middle < height blocks paths interior last) :
    Increasing (walk.concat adjacent) := by
  induction walk with
  | nil => exact ⟨strict, trivial⟩
  | cons adjacent rest previous => exact ⟨increasing.1, previous adjacent increasing.2 strict⟩

theorem forward_walk {blocks paths interior : ℕ} {first last : Vertex blocks paths interior}
    (reach : ForwardReachable blocks paths interior first last) :
    ∃ walk : (graph blocks paths interior (fun _ => true)).Walk first last, Increasing walk := by
  induction reach with
  | refl => exact ⟨.nil, trivial⟩
  | @tail middle last reach step previous =>
    obtain ⟨walk, increasing⟩ := previous
    obtain ⟨edge, equal⟩ := step
    have adjacent := graph_edge blocks paths interior (fun _ => true) edge rfl
    have strict := endpoint_height_strict blocks paths interior edge
    rw [equal] at adjacent strict
    exact ⟨walk.concat adjacent, increasing_concat walk adjacent increasing strict⟩

theorem increasing_support_lower {blocks paths interior : ℕ} {first last : Vertex blocks paths interior}
    (walk : (graph blocks paths interior (fun _ => true)).Walk first last)
    (increasing : Increasing walk) :
    ∀ vertex ∈ walk.support, height blocks paths interior first ≤ height blocks paths interior vertex := by
  induction walk with
  | nil => simp
  | cons adjacent rest previous =>
    intro vertex member
    simp only [SimpleGraph.Walk.support_cons, List.mem_cons] at member
    rcases member with equal | member
    · subst vertex; exact le_rfl
    · exact increasing.1.le.trans (previous increasing.2 vertex member)

theorem increasing_isPath {blocks paths interior : ℕ} {first last : Vertex blocks paths interior}
    (walk : (graph blocks paths interior (fun _ => true)).Walk first last)
    (increasing : Increasing walk) : walk.IsPath := by
  induction walk with
  | nil => exact SimpleGraph.Walk.IsPath.nil
  | @cons first middle last adjacent rest previous =>
    apply (SimpleGraph.Walk.cons_isPath_iff adjacent rest).mpr
    refine ⟨previous increasing.2, ?_⟩
    intro member
    exact not_lt_of_ge (increasing_support_lower rest increasing.2 first member) increasing.1

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

theorem forward_to_target (blocks paths interior : ℕ) (pathsPositive : 0 < paths)
    (vertex : Vertex blocks paths interior) :
    ForwardReachable blocks paths interior vertex (target blocks paths interior) := by
  have reach := forward_reflect blocks paths interior
    (forward_connected blocks paths interior pathsPositive (reflectVertex blocks paths interior vertex))
  rw [reflectVertex_involutive] at reach
  simpa [reflectVertex, source, target] using reach

theorem increasing_append {blocks paths interior : ℕ} {first middle last : Vertex blocks paths interior}
    (beforeWalk : (graph blocks paths interior (fun _ => true)).Walk first middle)
    (afterWalk : (graph blocks paths interior (fun _ => true)).Walk middle last)
    (beforeWalkIncreasing : Increasing beforeWalk) (afterWalkIncreasing : Increasing afterWalk) :
    Increasing (beforeWalk.append afterWalk) := by
  induction beforeWalk with
  | nil => exact afterWalkIncreasing
  | cons adjacent rest previous => exact ⟨beforeWalkIncreasing.1, previous afterWalk beforeWalkIncreasing.2 afterWalkIncreasing⟩

theorem canonical (blocks paths interior : ℕ) (pathsPositive : 0 < paths)
    (edge : Fin (Fintype.card (Edge blocks paths interior))) :
    ∃ walk : (network blocks paths interior).fullGraph.Walk
      (network blocks paths interior).source (network blocks paths interior).target,
      walk.IsPath ∧ s(((network blocks paths interior).endpoint edge).1,
        ((network blocks paths interior).endpoint edge).2) ∈ walk.edges := by
  let typedEdge := (Fintype.equivFin (Edge blocks paths interior)).symm edge
  obtain ⟨beforeWalk, beforeWalkIncreasing⟩ := forward_walk
    (forward_connected blocks paths interior pathsPositive (endpoint blocks paths interior typedEdge).1)
  obtain ⟨afterWalk, afterWalkIncreasing⟩ := forward_walk
    (forward_to_target blocks paths interior pathsPositive (endpoint blocks paths interior typedEdge).2)
  let middle : (graph blocks paths interior (fun _ => true)).Walk
      (endpoint blocks paths interior typedEdge).1 (endpoint blocks paths interior typedEdge).2 :=
    .cons (graph_edge blocks paths interior (fun _ => true) typedEdge rfl) .nil
  let walk := beforeWalk.append (middle.append afterWalk)
  have increasing : Increasing walk := increasing_append beforeWalk (middle.append afterWalk)
    beforeWalkIncreasing (increasing_append middle afterWalk
      ⟨endpoint_height_strict blocks paths interior typedEdge, trivial⟩ afterWalkIncreasing)
  have member : s((endpoint blocks paths interior typedEdge).1,
      (endpoint blocks paths interior typedEdge).2) ∈ walk.edges := by
    simp [walk, middle, SimpleGraph.Walk.edges_append]
  refine ⟨walk.map (graphIso blocks paths interior (fun _ => true)).toHom,
    (increasing_isPath walk increasing).map (Fintype.equivFin _).injective, ?_⟩
  simpa only [SimpleGraph.Walk.edges_map] using
    (List.mem_map.mpr ⟨_, member, rfl⟩ :
      s(((network blocks paths interior).endpoint edge).1,
        ((network blocks paths interior).endpoint edge).2) ∈
        walk.edges.map (Sym2.map (graphIso blocks paths interior (fun _ => true)).toHom))

def terminalSymmetry (blocks paths interior : ℕ) : (network blocks paths interior).NetworkSymmetry where
  vertex := ((Fintype.equivFin (Vertex blocks paths interior)).symm.trans
    (Function.Involutive.toPerm (reflectVertex blocks paths interior) (reflectVertex_involutive blocks paths interior))).trans
      (Fintype.equivFin (Vertex blocks paths interior))
  edge := ((Fintype.equivFin (Edge blocks paths interior)).symm.trans
    (Function.Involutive.toPerm (reflectEdge blocks paths interior) (reflectEdge_involutive blocks paths interior))).trans
      (Fintype.equivFin (Edge blocks paths interior))
  endpoint edge := by
    right
    simp only [network, Equiv.trans_apply, Function.Involutive.toPerm, Equiv.coe_fn_mk, Equiv.symm_apply_apply]
    rw [reflect_endpoint]

theorem classical (blocks paths interior : ℕ) (pathsPositive : 0 < paths) :
    (rule blocks paths interior).Classical where
  connected := network_connected blocks paths interior pathsPositive
  simple := simple blocks paths interior
  canonical := canonical blocks paths interior pathsPositive
  scale := by
    change 1 < (network blocks paths interior).fullGraph.dist
      (network blocks paths interior).source (network blocks paths interior).target
    rw [terminal_distance]; omega
  cut := one_edge_deletion_survives blocks paths interior pathsPositive
  symmetric := ⟨terminalSymmetry blocks paths interior, by
    intro vertex
    have formula (point : Fin (Fintype.card (Vertex blocks paths interior))) :
        (terminalSymmetry blocks paths interior).vertex point =
        (Fintype.equivFin (Vertex blocks paths interior))
          (reflectVertex blocks paths interior ((Fintype.equivFin _).symm point)) := rfl
    rw [formula, formula, Equiv.symm_apply_apply, reflectVertex_involutive, Equiv.apply_symm_apply], by
    change (terminalSymmetry blocks paths interior).vertex (network blocks paths interior).source =
      (network blocks paths interior).target
    simp [terminalSymmetry, Function.Involutive.toPerm, network, source, target, reflectVertex]⟩

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def appendixRule (base : ℝ) (length : ℕ) : Rule :=
  rule ⌈base ^ length⌉₊ ⌈(length : ℝ) * (4 / 3 : ℝ) ^ length⌉₊ (length - 2)

theorem appendixRule_classical (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length) :
    (appendixRule base length).Classical := by
  apply classical
  apply Nat.ceil_pos.mpr
  exact mul_pos (by exact_mod_cast (show 0 < length by omega)) (pow_pos (by norm_num) _)

theorem appendixRule_edges (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length) :
    (appendixRule base length).edges =
      4 + ⌈base ^ length⌉₊ * ⌈(length : ℝ) * (4 / 3 : ℝ) ^ length⌉₊ * length := by
  rw [appendixRule, rule_edges, Nat.sub_add_cancel lengthLarge]

theorem appendixRule_own_fixed_point (base : ℝ) (length : ℕ) (lengthLarge : 2 ≤ length) :
    ∃ probability : ℝ, 0 < probability ∧ probability < 1 ∧
      (appendixRule base length).network.reliability probability = probability :=
  (appendixRule_classical base length lengthLarge).exists_interior_fixed_point

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def ChainCrosses (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool) : Prop :=
  ∀ block : Fin blocks, ∃ path : Fin paths, ∀ edge : Fin (interior + 2),
    configuration (.inr (block, path, edge)) = true

def CircuitCrosses (blocks paths interior : ℕ) (configuration : Edge blocks paths interior → Bool) : Prop :=
  (configuration (.inl 0) = true ∧ configuration (.inl 1) = true) ∨
    (configuration (.inl 2) = true ∧ configuration (.inl 3) = true ∧
      ChainCrosses blocks paths interior configuration)

theorem circuit_chain_reachable (blocks paths interior : ℕ)
    (configuration : Edge blocks paths interior → Bool)
    (crosses : ChainCrosses blocks paths interior configuration) (junction : Fin (blocks + 1)) :
    (graph blocks paths interior configuration).Reachable (.inr (.inl 0)) (.inr (.inl junction)) := by
  induction junction using Fin.induction with
  | zero => exact .refl _
  | succ junction previous =>
    obtain ⟨path, opened⟩ := crosses junction
    apply previous.trans
    simpa [pathVertex] using
      path_reachable blocks paths interior configuration junction path opened (Fin.last (interior + 2))

theorem circuit_crossing_implies_reachable (blocks paths interior : ℕ)
    (configuration : Edge blocks paths interior → Bool)
    (crosses : CircuitCrosses blocks paths interior configuration) :
    (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (target blocks paths interior) := by
  rcases crosses with ⟨firstOpen, secondOpen⟩ | ⟨firstExterior, lastExterior, chain⟩
  · exact ⟨shortWalk blocks paths interior configuration firstOpen secondOpen⟩
  · have first := (graph_edge blocks paths interior configuration (.inl 2) firstExterior).reachable
    have last := (graph_edge blocks paths interior configuration (.inl 3) lastExterior).reachable
    exact (show (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (.inr (.inl 0)) from by simpa [endpoint] using first).trans
      ((circuit_chain_reachable blocks paths interior configuration chain (Fin.last blocks)).trans
        (by simpa [endpoint] using last))

theorem long_crossing_junction_active (blocks paths interior : ℕ)
    (configuration : Edge blocks paths interior → Bool)
    (firstExterior : configuration (.inl 2) = true)
    (chain : ChainCrosses blocks paths interior configuration) (junction : Fin (blocks + 1)) :
    (graph blocks paths interior configuration).Reachable
      (source blocks paths interior) (.inr (.inl junction)) := by
  have first := (graph_edge blocks paths interior configuration (.inl 2) firstExterior).reachable
  exact (show (graph blocks paths interior configuration).Reachable
    (source blocks paths interior) (.inr (.inl 0)) from by simpa [endpoint] using first).trans
    (circuit_chain_reachable blocks paths interior configuration chain junction)

theorem long_crossing_first_edge_retained (blocks paths interior : ℕ)
    (configuration : Edge blocks paths interior → Bool)
    (firstExterior : configuration (.inl 2) = true)
    (chain : ChainCrosses blocks paths interior configuration)
    (block : Fin blocks) (path : Fin paths)
    (firstOpen : configuration (.inr (block, path, 0)) = true) :
    (network blocks paths interior).childState .connected
      (fun edge => configuration ((Fintype.equivFin _).symm edge))
      (Fintype.equivFin _ (.inr (block, path, 0))) = some .connected := by
  have firstReach := long_crossing_junction_active blocks paths interior configuration
    firstExterior chain block.castSucc
  have adjacent := graph_edge blocks paths interior configuration (.inr (block, path, 0)) firstOpen
  have firstVertex : (endpoint blocks paths interior (.inr (block, path, 0))).1 =
      .inr (.inl block.castSucc) := by simp [endpoint, pathVertex]
  rw [← firstVertex] at firstReach
  have secondReach := firstReach.trans adjacent.reachable
  have firstActual := firstReach.map (graphIso blocks paths interior configuration).toHom
  have secondActual := secondReach.map (graphIso blocks paths interior configuration).toHom
  have firstActive := ((network blocks paths interior).openGraph
    (fun edge => configuration ((Fintype.equivFin _).symm edge))).reachableDecide_eq_true _ _ |>.mpr firstActual
  have secondActive := ((network blocks paths interior).openGraph
    (fun edge => configuration ((Fintype.equivFin _).symm edge))).reachableDecide_eq_true _ _ |>.mpr secondActual
  change ((network blocks paths interior).openGraph
    (fun edge => configuration ((Fintype.equivFin _).symm edge))).reachableDecide
    (network blocks paths interior).source
    ((Fintype.equivFin (Vertex blocks paths interior))
      (endpoint blocks paths interior (.inr (block, path, 0))).1) = true at firstActive
  change ((network blocks paths interior).openGraph
    (fun edge => configuration ((Fintype.equivFin _).symm edge))).reachableDecide
    (network blocks paths interior).source
    ((Fintype.equivFin (Vertex blocks paths interior))
      (endpoint blocks paths interior (.inr (block, path, 0))).2) = true at secondActive
  simp [childState, active, network, Equiv.symm_apply_apply, firstOpen] at firstActive secondActive ⊢
  simp only [firstActive, secondActive, Bool.true_and, Bool.true_or, if_true]
  trivial

end
end IGSIII4.SpectralDensity.ActualFamily

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open Universality Universality.FiniteNetwork

def firstEdgeIndex (blocks paths interior : ℕ) (pair : Fin blocks × Fin paths) :
    Fin (Fintype.card (Edge blocks paths interior)) :=
  Fintype.equivFin _ (.inr (pair.1, pair.2, 0))

theorem firstEdgeIndex_injective (blocks paths interior : ℕ) :
    Function.Injective (firstEdgeIndex blocks paths interior) := by
  intro first second equal
  have typed := (Fintype.equivFin (Edge blocks paths interior)).injective equal
  simp only [Sum.inr.injEq, Prod.mk.injEq] at typed
  exact Prod.ext typed.1 typed.2.1

theorem liveCount_first_edges_lower (blocks paths interior : ℕ)
    (configuration : Edge blocks paths interior → Bool)
    (firstExterior : configuration (.inl 2) = true)
    (chain : ChainCrosses blocks paths interior configuration) :
    (Finset.univ.filter (fun pair : Fin blocks × Fin paths =>
      configuration (.inr (pair.1, pair.2, 0)) = true)).card ≤
    (network blocks paths interior).liveCount .connected .connected
      (fun edge => configuration ((Fintype.equivFin _).symm edge)) := by
  have included : (Finset.univ.filter (fun pair : Fin blocks × Fin paths =>
      configuration (.inr (pair.1, pair.2, 0)) = true)).image (firstEdgeIndex blocks paths interior) ⊆
      Finset.univ.filter (fun edge => (network blocks paths interior).childState .connected
        (fun edge => configuration ((Fintype.equivFin _).symm edge)) edge = some .connected) := by
    intro edge member
    obtain ⟨pair, pairMember, rfl⟩ := Finset.mem_image.mp member
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, long_crossing_first_edge_retained blocks paths interior configuration
      firstExterior chain pair.1 pair.2 (Finset.mem_filter.mp pairMember).2⟩
  rw [← Finset.card_image_of_injective _ (firstEdgeIndex_injective blocks paths interior)]
  exact Finset.card_le_card included

end
end IGSIII4.SpectralDensity.ActualFamily
