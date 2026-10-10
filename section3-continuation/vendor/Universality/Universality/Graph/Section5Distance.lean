import Universality.Section5.WheatstoneResponse
import Universality.Graph.DistanceCertificate

set_option backward.isDefEq.respectTransparency false

namespace Universality.FiniteNetwork
noncomputable section

variable {outerVertices outerEdges : ℕ}
variable {innerVertices innerEdges : Fin outerEdges → ℕ}
variable (R : FiniteNetwork outerVertices outerEdges)
variable (S : (edge : Fin outerEdges) → FiniteNetwork (innerVertices edge) (innerEdges edge))

private theorem clamp_height_bound (first second delta : ℤ)
    (bound : |first - second| ≤ 1) :
    |max (-first) (min first delta) - max (-second) (min second delta)| ≤ 1 := by
  rw [abs_le] at bound ⊢
  constructor <;> omega

def heterogeneousHeight (height : Fin outerVertices → ℤ)
    (certificates : ∀ edge, (S edge).DistanceCertificate) : R.HeterogeneousVertex S → ℤ
  | .inl vertex => height vertex
  | .inr ⟨edge, vertex⟩ =>
      height (R.endpoint edge).1 + max (-(certificates edge).height vertex.val)
        (min ((certificates edge).height vertex.val)
          (height (R.endpoint edge).2 - height (R.endpoint edge).1))

theorem heterogeneousHeight_cell (height : Fin outerVertices → ℤ)
    (certificates : ∀ edge, (S edge).DistanceCertificate)
    (bounds : ∀ edge, |height (R.endpoint edge).2 - height (R.endpoint edge).1| ≤
      (certificates edge).length) (edge : Fin outerEdges) (vertex : Fin (innerVertices edge)) :
    R.heterogeneousHeight S height certificates (R.heterogeneousCellVertex S edge vertex) =
      height (R.endpoint edge).1 + max (-(certificates edge).height vertex)
        (min ((certificates edge).height vertex)
          (height (R.endpoint edge).2 - height (R.endpoint edge).1)) := by
  by_cases source : vertex = (S edge).source
  · subst vertex
    rw [heterogeneousCellVertex_source]
    simp [heterogeneousHeight, (certificates edge).source_height]
  · by_cases target : vertex = (S edge).target
    · subst vertex
      rw [heterogeneousCellVertex_target]
      simp only [heterogeneousHeight, (certificates edge).target_height]
      have bound := bounds edge
      rw [abs_le] at bound
      rw [min_eq_right bound.2, max_eq_right bound.1]
      ring
    · simp [heterogeneousCellVertex, source, target, heterogeneousHeight]

theorem heterogeneousHeight_edge_bound (height : Fin outerVertices → ℤ)
    (certificates : ∀ edge, (S edge).DistanceCertificate)
    (bounds : ∀ edge, |height (R.endpoint edge).2 - height (R.endpoint edge).1| ≤
      (certificates edge).length) (edge : Fin outerEdges) (child : Fin (innerEdges edge)) :
    |R.heterogeneousHeight S height certificates
        (R.heterogeneousCellVertex S edge ((S edge).endpoint child).1) -
      R.heterogeneousHeight S height certificates
        (R.heterogeneousCellVertex S edge ((S edge).endpoint child).2)| ≤ 1 := by
  rw [heterogeneousHeight_cell, heterogeneousHeight_cell]
  · simpa only [add_sub_add_left_eq_sub] using
      clamp_height_bound ((certificates edge).height ((S edge).endpoint child).1)
        ((certificates edge).height ((S edge).endpoint child).2)
        (height (R.endpoint edge).2 - height (R.endpoint edge).1)
        ((certificates edge).edge_bound child)
  · exact bounds
  · exact bounds

def heterogeneousCellWalk (certificates : ∀ edge, (S edge).DistanceCertificate) (edge : Fin outerEdges) :
    (R.heterogeneousSubstitutedGraph S (fun _ _ => true)).Walk
      (Sum.inl (R.endpoint edge).1) (Sum.inl (R.endpoint edge).2) :=
  ((certificates edge).walk.map (R.heterogeneousCellHom S (fun _ _ => true) edge)).copy
    (R.heterogeneousCellVertex_source S edge) (R.heterogeneousCellVertex_target S edge)

theorem heterogeneousCellWalk_length (certificates : ∀ edge, (S edge).DistanceCertificate)
    (edge : Fin outerEdges) :
    (R.heterogeneousCellWalk S certificates edge).length = (certificates edge).length := by
  rw [heterogeneousCellWalk, SimpleGraph.Walk.length_copy, SimpleGraph.Walk.length_map]
  exact (certificates edge).walk_length

def heterogeneousDistanceCertificate (height : Fin outerVertices → ℤ)
    (certificates : ∀ edge, (S edge).DistanceCertificate) (length : ℕ)
    (source_height : height R.source = 0) (target_height : height R.target = length)
    (bounds : ∀ edge, |height (R.endpoint edge).2 - height (R.endpoint edge).1| ≤
      (certificates edge).length)
    (walk : (R.heterogeneousSubstitutedGraph S (fun _ _ => true)).Walk
      (Sum.inl R.source) (Sum.inl R.target)) (walk_length : walk.length = length) :
    (R.heterogeneousSubstitute S).DistanceCertificate where
  length := length
  height vertex := R.heterogeneousHeight S height certificates ((Fintype.equivFin _).symm vertex)
  source_height := by simpa [heterogeneousSubstitute, heterogeneousHeight] using source_height
  target_height := by simpa [heterogeneousSubstitute, heterogeneousHeight] using target_height
  edge_bound edge := by
    obtain ⟨⟨edge, child⟩, rfl⟩ := (Fintype.equivFin (Σ edge, Fin (innerEdges edge))).surjective edge
    simpa only [heterogeneousSubstitute_endpoint, Equiv.symm_apply_apply] using
      R.heterogeneousHeight_edge_bound S height certificates bounds edge child
  walk := walk.map (R.heterogeneousGraphIso S (fun _ _ => true)).toHom
  walk_length := by rw [SimpleGraph.Walk.length_map]; exact walk_length

end
end Universality.FiniteNetwork

namespace Universality.Section5
noncomputable section
open FiniteNetwork

def wheatstoneChildCertificates (a b c : Rule)
    (first : a.network.DistanceCertificate) (second : b.network.DistanceCertificate)
    (central : c.network.DistanceCertificate) :
    ∀ edge : Fin 5, (![a,b,b,a,c] edge).network.DistanceCertificate :=
  Fin.cases first (Fin.cases second (Fin.cases second (Fin.cases first
    (Fin.cases central (fun edge => Fin.elim0 edge)))))

def wheatstoneDistanceCertificate (a b c : Rule)
    (first : a.network.DistanceCertificate) (second : b.network.DistanceCertificate)
    (central : c.network.DistanceCertificate) : (wheatstoneRule a b c).network.DistanceCertificate := by
  let certificates := wheatstoneChildCertificates a b c first second central
  let cells := fun edge : Fin 5 => (![a,b,b,a,c] edge).network
  let height : Fin 4 → ℤ := ![0,
    min (first.length + second.length) (min (2 * first.length + central.length)
      (2 * second.length + central.length)),
    min first.length (second.length + central.length),
    min second.length (first.length + central.length)]
  let upper : (wheatstoneNetwork.heterogeneousSubstitutedGraph cells (fun _ _ => true)).Walk
      (Sum.inl 0) (Sum.inl 1) :=
    (wheatstoneNetwork.heterogeneousCellWalk cells certificates 0).append
      (wheatstoneNetwork.heterogeneousCellWalk cells certificates 1)
  let throughCentralA : (wheatstoneNetwork.heterogeneousSubstitutedGraph cells (fun _ _ => true)).Walk
      (Sum.inl 0) (Sum.inl 1) :=
    (wheatstoneNetwork.heterogeneousCellWalk cells certificates 0).append
      ((wheatstoneNetwork.heterogeneousCellWalk cells certificates 4).append
        (wheatstoneNetwork.heterogeneousCellWalk cells certificates 3))
  let throughCentralB : (wheatstoneNetwork.heterogeneousSubstitutedGraph cells (fun _ _ => true)).Walk
      (Sum.inl 0) (Sum.inl 1) :=
    (wheatstoneNetwork.heterogeneousCellWalk cells certificates 2).append
      ((wheatstoneNetwork.heterogeneousCellWalk cells certificates 4).reverse.append
        (wheatstoneNetwork.heterogeneousCellWalk cells certificates 1))
  have upper_length : upper.length = first.length + second.length := by
    simp only [upper, SimpleGraph.Walk.length_append, heterogeneousCellWalk_length]
    rfl
  have central_a_length : throughCentralA.length = 2 * first.length + central.length := by
    simp only [throughCentralA, SimpleGraph.Walk.length_append, heterogeneousCellWalk_length]
    change first.length + (central.length + first.length) = _
    omega
  have central_b_length : throughCentralB.length = 2 * second.length + central.length := by
    simp only [throughCentralB, SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      heterogeneousCellWalk_length]
    change second.length + (central.length + second.length) = _
    omega
  have bounds : ∀ edge : Fin 5,
      |height (wheatstoneNetwork.endpoint edge).2 - height (wheatstoneNetwork.endpoint edge).1| ≤
        (certificates edge).length := by
    intro edge
    fin_cases edge
    · change |min (first.length : ℤ) (second.length + central.length) - 0| ≤ first.length
      rw [abs_le]
      constructor <;> omega
    · change |min ((first.length : ℤ) + second.length)
          (min (2 * first.length + central.length) (2 * second.length + central.length)) -
          min (first.length : ℤ) (second.length + central.length)| ≤ second.length
      rw [abs_le]
      constructor <;> omega
    · change |min (second.length : ℤ) (first.length + central.length) - 0| ≤ second.length
      rw [abs_le]
      constructor <;> omega
    · change |min ((first.length : ℤ) + second.length)
          (min (2 * first.length + central.length) (2 * second.length + central.length)) -
          min (second.length : ℤ) (first.length + central.length)| ≤ first.length
      rw [abs_le]
      constructor <;> omega
    · change |min (second.length : ℤ) (first.length + central.length) -
          min (first.length : ℤ) (second.length + central.length)| ≤ central.length
      rw [abs_le]
      constructor <;> omega
  have source_height : height wheatstoneNetwork.source = 0 := rfl
  have target_height : height wheatstoneNetwork.target =
      (min (first.length + second.length) (min (2 * first.length + central.length)
        (2 * second.length + central.length)) : ℕ) := by
    simp only [Nat.cast_min, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    rfl
  let shortest : {walk : (wheatstoneNetwork.heterogeneousSubstitutedGraph cells
      (fun _ _ => true)).Walk (Sum.inl 0) (Sum.inl 1) //
      walk.length = min (first.length + second.length) (min (2 * first.length + central.length)
        (2 * second.length + central.length))} := by
    by_cases upper_minimal : first.length + second.length ≤
        min (2 * first.length + central.length) (2 * second.length + central.length)
    · exact ⟨upper, by rw [upper_length, min_eq_left upper_minimal]⟩
    · by_cases central_minimal : 2 * first.length + central.length ≤ 2 * second.length + central.length
      · exact ⟨throughCentralA, by rw [central_a_length, min_eq_right (by omega), min_eq_left central_minimal]⟩
      · exact ⟨throughCentralB, by rw [central_b_length, min_eq_right (by omega), min_eq_right (by omega)]⟩
  exact wheatstoneNetwork.heterogeneousDistanceCertificate cells height certificates
    (min (first.length + second.length) (min (2 * first.length + central.length)
      (2 * second.length + central.length))) source_height target_height bounds shortest.val shortest.property

theorem wheatstoneRule_distance (a b c : Rule)
    (first_connected : a.network.fullGraph.Reachable a.network.source a.network.target)
    (second_connected : b.network.fullGraph.Reachable b.network.source b.network.target)
    (central_connected : c.network.fullGraph.Reachable c.network.source c.network.target) :
    (wheatstoneRule a b c).network.fullGraph.dist (wheatstoneRule a b c).network.source
      (wheatstoneRule a b c).network.target =
      min (a.network.fullGraph.dist a.network.source a.network.target +
          b.network.fullGraph.dist b.network.source b.network.target)
        (min (2 * a.network.fullGraph.dist a.network.source a.network.target +
            c.network.fullGraph.dist c.network.source c.network.target)
          (2 * b.network.fullGraph.dist b.network.source b.network.target +
            c.network.fullGraph.dist c.network.source c.network.target)) :=
  (wheatstoneDistanceCertificate a b c
    (DistanceCertificate.ofReachable a.network first_connected)
    (DistanceCertificate.ofReachable b.network second_connected)
    (DistanceCertificate.ofReachable c.network central_connected)).distance_eq _

end
end Universality.Section5
