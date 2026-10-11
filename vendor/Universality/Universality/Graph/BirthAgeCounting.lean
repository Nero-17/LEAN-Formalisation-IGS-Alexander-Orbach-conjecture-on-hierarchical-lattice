import Universality.Graph.BirthAddress
import Universality.Graph.FiniteVolume

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

instance birthAddressFintype (rule : Rule) : (n : ℕ) → Fintype (rule.BirthAddress n)
  | 0 => inferInstanceAs (Fintype rule.network.InteriorVertex)
  | n + 1 =>
    letI := rule.birthAddressFintype n
    inferInstanceAs (Fintype (rule.network.InteriorVertex ⊕ (Fin rule.edges × rule.BirthAddress n)))

def birthAgeCount (rule : Rule) (depth age : ℕ) : ℕ :=
  ∑ address : rule.BirthAddress depth, if BirthAddress.age rule depth address = age then 1 else 0

theorem birthAgeCount_zero (rule : Rule) (age : ℕ) :
    rule.birthAgeCount 0 age = if 0 = age then rule.vertices - 2 else 0 := by
  classical
  change (∑ _ : rule.network.InteriorVertex, if 0 = age then (1 : ℕ) else 0) = _
  by_cases h : 0 = age
  · simp [birthAgeCount, BirthAddress.age, h, rule.network.card_interior_vertices]
  · simp [birthAgeCount, BirthAddress.age, h]

theorem birthAgeCount_succ (rule : Rule) (depth age : ℕ) :
    rule.birthAgeCount (depth + 1) age =
      (if depth + 1 = age then rule.vertices - 2 else 0) + rule.edges * rule.birthAgeCount depth age := by
  classical
  change (∑ address : rule.network.InteriorVertex ⊕ (Fin rule.edges × rule.BirthAddress depth),
    if BirthAddress.age rule (depth + 1) address = age then 1 else 0) = _
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  simp only [BirthAddress.age]
  by_cases h : depth + 1 = age
  · simp [h, birthAgeCount, rule.network.card_interior_vertices]
  · simp [h, birthAgeCount]

theorem birthAgeCount_eq_zero_of_lt (rule : Rule) (depth age : ℕ) (h : depth < age) :
    rule.birthAgeCount depth age = 0 := by
  apply Finset.sum_eq_zero
  intro address _
  have hne : BirthAddress.age rule depth address ≠ age :=
    ne_of_lt ((BirthAddress.age_le rule depth address).trans_lt h)
  simp only [if_neg hne]

theorem birthAgeCount_self (rule : Rule) (depth : ℕ) :
    rule.birthAgeCount depth depth = rule.vertices - 2 := by
  cases depth with
  | zero => simp [rule.birthAgeCount_zero]
  | succ depth =>
    rw [rule.birthAgeCount_succ, if_pos rfl,
      rule.birthAgeCount_eq_zero_of_lt depth (depth + 1) (Nat.lt_succ_self depth), mul_zero, add_zero]

/-- The geometric age weights are derived from the actual finite birth-address
fibres: there are exactly this many vertices of each possible age. -/
theorem birthAgeCount_eq (rule : Rule) (depth age : ℕ) (hage : age ≤ depth) :
    rule.birthAgeCount depth age = (rule.vertices - 2) * rule.edges ^ (depth - age) := by
  induction depth generalizing age with
  | zero =>
    have heq : age = 0 := Nat.eq_zero_of_le_zero hage
    subst age
    simpa using rule.birthAgeCount_self 0
  | succ depth ih =>
    by_cases heq : age = depth + 1
    · subst age
      simpa using rule.birthAgeCount_self (depth + 1)
    · have hle : age ≤ depth := by omega
      rw [rule.birthAgeCount_succ, if_neg (Ne.symm heq), zero_add, ih age hle]
      have hsub : depth + 1 - age = (depth - age) + 1 := by omega
      rw [hsub, pow_succ]
      ring

/-- Exact count for the actual generation's interior vertices, not merely for
an independently postulated address model. -/
theorem card_interiorVertexAge (rule : Rule) (depth age : ℕ) (hage : age ≤ depth) :
    Fintype.card {v : (rule.generation depth).network.InteriorVertex //
      rule.interiorVertexAge depth v = age} =
      (rule.vertices - 2) * rule.edges ^ (depth - age) := by
  classical
  rw [← rule.birthAgeCount_eq depth age hage]
  rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  change (∑ v : (rule.generation depth).network.InteriorVertex,
    if BirthAddress.age rule depth (rule.generationInteriorAddressEquiv depth v) = age then 1 else 0) = _
  exact (rule.generationInteriorAddressEquiv depth).sum_comp
    (fun address => if BirthAddress.age rule depth address = age then 1 else 0)

end
end Universality.Rule
