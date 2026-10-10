import Universality.Percolation.ConnectivityCertificate

namespace Universality.FiniteNetwork

structure ComponentRow (vertices edges : ℕ) where
  index : Fin (2 ^ edges)
  sourceComponent : ConnectivityCertificate vertices edges
  targetComponent : ConnectivityCertificate vertices edges

variable {vertices edges : ℕ} (R : FiniteNetwork vertices edges)

def ComponentRow.configuration (row : ComponentRow vertices edges) : Configuration edges :=
  decodeConfiguration (BitVec.ofFin row.index)

def ComponentRow.Valid (row : ComponentRow vertices edges) : Prop :=
  row.sourceComponent.Valid R row.configuration R.source ∧
    row.targetComponent.Valid R row.configuration R.target

instance (row : ComponentRow vertices edges) : Decidable (row.Valid R) := by
  unfold ComponentRow.Valid
  infer_instance

def ComponentRow.condition (row : ComponentRow vertices edges) (σ : LiveState) : Bool :=
  let crossing := row.sourceComponent.mask.getLsbD R.target.val
  match σ with | .connected => crossing | .both | .single => !crossing

def ComponentRow.active (row : ComponentRow vertices edges) (σ : LiveState)
    (v : Fin vertices) : Bool :=
  row.sourceComponent.mask.getLsbD v.val ||
    (σ == .both && row.targetComponent.mask.getLsbD v.val)

def ComponentRow.childState (row : ComponentRow vertices edges) (σ : LiveState)
    (e : Fin edges) : Option LiveState :=
  let first := row.active σ (R.endpoint e).1
  let second := row.active σ (R.endpoint e).2
  if first && second then
    if row.configuration e then some .connected else some .both
  else if first || second then some .single else none

def ComponentRow.count (row : ComponentRow vertices edges) (σ τ : LiveState) : ℕ :=
  if row.condition R σ then
    (Finset.univ.filter fun e => row.childState R σ e = some τ).card
  else 0

theorem ComponentRow.condition_eq (row : ComponentRow vertices edges)
    (valid : row.Valid R) (σ : LiveState) :
    row.condition R σ = R.conditioning σ row.configuration := by
  have hs := row.sourceComponent.reachableDecide_eq R row.configuration R.source valid.1 R.target
  cases σ <;> simp only [ComponentRow.condition, conditioning, crosses, hs]

theorem ComponentRow.active_eq (row : ComponentRow vertices edges)
    (valid : row.Valid R) (σ : LiveState) (v : Fin vertices) :
    row.active σ v = R.active σ row.configuration v := by
  rw [FiniteNetwork.active, row.sourceComponent.reachableDecide_eq R _ _ valid.1,
    row.targetComponent.reachableDecide_eq R _ _ valid.2]
  rfl

theorem ComponentRow.childState_eq (row : ComponentRow vertices edges)
    (valid : row.Valid R) (σ : LiveState) (e : Fin edges) :
    row.childState R σ e = R.childState σ row.configuration e := by
  simp only [ComponentRow.childState, FiniteNetwork.childState, row.active_eq R valid]

theorem ComponentRow.count_eq (row : ComponentRow vertices edges)
    (valid : row.Valid R) (σ τ : LiveState) :
    row.count R σ τ =
      if R.conditioning σ row.configuration then R.liveCount σ τ row.configuration else 0 := by
  simp only [ComponentRow.count, liveCount, row.condition_eq R valid,
    row.childState_eq R valid]

theorem sum_component_rows {α : Type*} [AddCommMonoid α]
    (rows : List (ComponentRow vertices edges))
    (indices : rows.map ComponentRow.index = List.finRange (2 ^ edges))
    (response : ComponentRow vertices edges → α) (trueResponse : Configuration edges → α)
    (hresponse : ∀ row ∈ rows, response row = trueResponse row.configuration) :
    (rows.map response).sum = ∑ ω : Configuration edges, trueResponse ω := by
  classical
  have hmap : rows.map response =
      (rows.map ComponentRow.index).map
        (fun index => trueResponse (decodeConfiguration (BitVec.ofFin index))) := by
    rw [List.map_map]
    apply List.map_congr_left
    exact hresponse
  rw [hmap, indices]
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]
  apply Fintype.sum_equiv (configurationIndexEquiv edges).symm
  intro index
  rfl

theorem certified_conditioningCount
    (rows : List (ComponentRow vertices edges))
    (indices : rows.map ComponentRow.index = List.finRange (2 ^ edges))
    (valid : ∀ row ∈ rows, row.Valid R) (σ : LiveState) :
    (rows.map fun row => if row.condition R σ then 1 else 0).sum = R.conditioningCount σ := by
  rw [conditioningCount, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply sum_component_rows rows indices
  intro row hrow
  rw [row.condition_eq R (valid row hrow)]

theorem certified_conditionalCount
    (rows : List (ComponentRow vertices edges))
    (indices : rows.map ComponentRow.index = List.finRange (2 ^ edges))
    (valid : ∀ row ∈ rows, row.Valid R) (σ τ : LiveState) :
    (rows.map fun row => row.count R σ τ).sum = R.conditionalCount σ τ := by
  unfold conditionalCount
  apply sum_component_rows rows indices
  intro row hrow
  exact row.count_eq R (valid row hrow) σ τ

end Universality.FiniteNetwork
