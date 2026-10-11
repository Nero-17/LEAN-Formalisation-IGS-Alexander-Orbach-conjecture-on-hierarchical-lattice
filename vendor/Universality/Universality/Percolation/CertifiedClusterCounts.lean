import Universality.Percolation.ConnectivityCertificate
import Universality.Percolation.ClusterNumberPolynomial
import Universality.Percolation.ClusterRepresentatives

namespace Universality.FiniteNetwork

structure FullComponentRow (vertices edges : ℕ) where
  index : Fin (2 ^ edges)
  component : Fin vertices → ConnectivityCertificate vertices edges

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def FullComponentRow.configuration (row : FullComponentRow vertices edges) : Configuration edges :=
  decodeConfiguration (BitVec.ofFin row.index)

def FullComponentRow.Valid (row : FullComponentRow vertices edges) : Prop :=
  ∀ root, (row.component root).Valid R row.configuration root

instance fullComponentRowDecidableValid (row : FullComponentRow vertices edges) : Decidable (row.Valid R) := by
  unfold FullComponentRow.Valid
  infer_instance

def FullComponentRow.componentVertices (row : FullComponentRow vertices edges) (root : Fin vertices) :
    Finset (Fin vertices) :=
  Finset.univ.filter fun vertex => (row.component root).mask.getLsbD vertex.val

def FullComponentRow.internalCount (row : FullComponentRow vertices edges) : ℕ :=
  (Finset.univ.filter fun root : Fin vertices =>
    (row.component root).mask.getLsbD R.source.val = false ∧
    (row.component root).mask.getLsbD R.target.val = false ∧
    ∀ vertex : Fin vertices, (row.component root).mask.getLsbD vertex.val = true → root ≤ vertex).card

theorem FullComponentRow.componentVertices_eq (row : FullComponentRow vertices edges)
    (valid : row.Valid R) (root : Fin vertices) :
    row.componentVertices root = R.clusterVertices row.configuration root := by
  ext vertex
  simp only [FullComponentRow.componentVertices, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [R.mem_clusterVertices, (row.component root).reachable_iff R _ root (valid root)]

theorem FullComponentRow.internalCount_eq (row : FullComponentRow vertices edges)
    (valid : row.Valid R) : row.internalCount R = (R.internalClusterFamily row.configuration).card := by
  rw [R.internalClusterFamily_card_representatives]
  unfold FullComponentRow.internalCount
  congr 1
  ext root
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  simp_rw [← row.componentVertices_eq R valid]
  simp [FullComponentRow.componentVertices]

theorem certified_internalClusterCountByOpenSize (rows : List (FullComponentRow vertices edges))
    (indices : rows.map FullComponentRow.index = List.finRange (2 ^ edges))
    (valid : ∀ row ∈ rows, row.Valid R) (k : ℕ) :
    (rows.map fun row => if openCount row.configuration = k then row.internalCount R else 0).sum =
      R.internalClusterCountByOpenSize k := by
  classical
  have hmap : (rows.map fun row => if openCount row.configuration = k then row.internalCount R else 0) =
      (rows.map FullComponentRow.index).map (fun index =>
        if openCount (decodeConfiguration (BitVec.ofFin index)) = k then
          (R.internalClusterFamily (decodeConfiguration (BitVec.ofFin index))).card else 0) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro row hrow
    rw [row.internalCount_eq R (valid row hrow)]
    rfl
  rw [hmap, indices, ← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  unfold internalClusterCountByOpenSize
  apply Fintype.sum_equiv (configurationIndexEquiv edges).symm
  intro index
  rfl

end Universality.FiniteNetwork
