import Universality.Section5.AllocationMatrices
import Universality.Algebra.GroupedWords
import Mathlib.Data.List.Nodup

namespace Universality.Section5
noncomputable section

/-- Lexicographically ordered ternary addresses above one binary word. -/
def projectedAddresses : List Bool → List (List (Fin 3))
  | [] => [[]]
  | false :: word => (projectedAddresses word).map (0 :: ·) ++ (projectedAddresses word).map (1 :: ·)
  | true :: word => (projectedAddresses word).map (2 :: ·)

theorem projectedAddresses_length (word : List Bool) :
    (projectedAddresses word).length = 2 ^ zeroCount word := by
  induction word with
  | nil => simp [projectedAddresses, zeroCount]
  | cons bit word induction_hypothesis =>
      cases bit <;> simp [projectedAddresses, induction_hypothesis, pow_succ, Nat.mul_two]

theorem mem_projectedAddresses (address : List (Fin 3)) (word : List Bool) :
    address ∈ projectedAddresses word ↔ projectedAddress address = word := by
  induction word generalizing address with
  | nil => cases address <;> simp [projectedAddresses, projectedAddress]
  | cons bit word induction_hypothesis =>
      cases address with
      | nil => cases bit <;> simp [projectedAddresses, projectedAddress]
      | cons letter address =>
          cases bit <;> fin_cases letter <;>
            simp [projectedAddresses, List.mem_map, List.cons.injEq, projectedAddress,
              ] <;> exact induction_hypothesis address

theorem projectedAddresses_nodup (word : List Bool) : (projectedAddresses word).Nodup := by
  induction word with
  | nil => simp [projectedAddresses]
  | cons bit word induction_hypothesis =>
      cases bit
      · apply List.Nodup.append
        · exact induction_hypothesis.map (by intro a b equal; exact List.cons.inj equal |>.2)
        · exact induction_hypothesis.map (by intro a b equal; exact List.cons.inj equal |>.2)
        · apply List.disjoint_left.mpr
          intro address first second
          obtain ⟨a, _, rfl⟩ := List.mem_map.mp first
          obtain ⟨b, _, equal⟩ := List.mem_map.mp second
          have impossible := (List.cons.inj equal).1
          exact (by decide : (1 : Fin 3) ≠ 0) impossible
      · exact induction_hypothesis.map (by intro a b equal; exact List.cons.inj equal |>.2)

theorem sum_ternaryAddresses_by_projection {R : Type*} [AddCommMonoid R]
    (n : ℕ) (response : List (Fin 3) → R) :
    ((ternaryAddresses n).map response).sum =
      ((binaryWords n).map (fun word => ((projectedAddresses word).map response).sum)).sum := by
  induction n generalizing response with
  | zero => simp [ternaryAddresses, binaryWords, projectedAddresses]
  | succ n induction_hypothesis =>
      simp only [ternaryAddresses, binaryWords, projectedAddresses, List.map_append,
        List.map_map, Function.comp_def, List.sum_append]
      simp only [induction_hypothesis, List.sum_map_add]

/-- Decorate precisely the first allocation(word) addresses in each projection fibre. -/
def allocationDecoration (allocation : List Bool → ℕ) (address : List (Fin 3)) : Bool :=
  decide (address ∈ (projectedAddresses (projectedAddress address)).take (allocation (projectedAddress address)))

end
end Universality.Section5
