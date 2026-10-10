import Universality.Percolation.BitConnectivity

namespace Universality.FiniteNetwork

def encodeConfiguration {edges : ℕ} (ω : Configuration edges) : BitVec edges :=
  (BitVec.ofBoolListLE (List.ofFn ω)).setWidth edges

def decodeConfiguration {edges : ℕ} (bits : BitVec edges) : Configuration edges :=
  fun e => bits.getLsbD e.val

theorem decode_encode_configuration {edges : ℕ} (ω : Configuration edges) :
    decodeConfiguration (encodeConfiguration ω) = ω := by
  ext e
  simp only [decodeConfiguration, encodeConfiguration, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, e.isLt]
  simp

theorem encode_decode_configuration {edges : ℕ} (bits : BitVec edges) :
    encodeConfiguration (decodeConfiguration bits) = bits := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simpa only [decodeConfiguration] using congrFun
    (decode_encode_configuration (decodeConfiguration bits)) ⟨i, hi⟩

def configurationIndexEquiv (edges : ℕ) : Configuration edges ≃ Fin (2 ^ edges) where
  toFun ω := (encodeConfiguration ω).toFin
  invFun index := decodeConfiguration (BitVec.ofFin index)
  left_inv ω := by simpa using decode_encode_configuration ω
  right_inv index := by
    have h := congrArg BitVec.toFin (encode_decode_configuration (BitVec.ofFin index))
    simpa only [BitVec.toFin_ofFin] using h

def indexedConditioningCount {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (σ : LiveState) : ℕ :=
  ∑ index : Fin (2 ^ edges),
    let ω := decodeConfiguration (BitVec.ofFin index)
    let crossing := R.bitReachable ω R.source R.target
    if (match σ with | .connected => crossing | .both | .single => !crossing)
    then 1 else 0

theorem indexedConditioningCount_eq {vertices edges : ℕ}
    (R : FiniteNetwork vertices edges) (σ : LiveState) :
    R.indexedConditioningCount σ = R.conditioningCount σ := by
  rw [← bitConditioningCount_eq]
  unfold indexedConditioningCount bitConditioningCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Fintype.sum_equiv (configurationIndexEquiv edges).symm
  intro index
  rfl

end Universality.FiniteNetwork
