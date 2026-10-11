import Universality.Graph.BirthAgeCounting

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

def BirthAgeFiber (rule : Rule) (depth age : ℕ) :=
  {address : rule.BirthAddress depth // BirthAddress.age rule depth address = age}

/-- The oldest birth fibre consists exactly of the original interior vertices. -/
def birthAgeFiberSelfEquiv (rule : Rule) (depth : ℕ) :
    rule.BirthAgeFiber depth depth ≃ rule.network.InteriorVertex := by
  cases depth with
  | zero =>
    exact {
      toFun := fun address => address.val
      invFun := fun vertex => ⟨vertex, rfl⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  | succ depth =>
    refine {
      toFun := fun address => ?_
      invFun := fun vertex => ⟨Sum.inl vertex, rfl⟩
      left_inv := ?_
      right_inv := ?_ }
    · rcases address with ⟨vertex | child, hage⟩
      · exact vertex
      · have hle := BirthAddress.age_le rule depth child.2
        change BirthAddress.age rule depth child.2 = depth + 1 at hage
        omega
    · rintro ⟨vertex | child, hage⟩
      · rfl
      · have hle := BirthAddress.age_le rule depth child.2
        change BirthAddress.age rule depth child.2 = depth + 1 at hage
        omega
    · intro vertex
      rfl

/-- Conditional on a strictly younger age, the first ancestral symbol is a
freely chosen indexed edge and the remaining address lies in the smaller fibre. -/
def birthAgeFiberChildEquiv (rule : Rule) (depth age : ℕ) (hage : age ≤ depth) :
    rule.BirthAgeFiber (depth + 1) age ≃ Fin rule.edges × rule.BirthAgeFiber depth age where
  toFun address := by
    rcases address with ⟨vertex | child, heq⟩
    · change depth + 1 = age at heq
      omega
    · exact ⟨child.1, child.2, heq⟩
  invFun child := ⟨Sum.inr (child.1, child.2.val), child.2.property⟩
  left_inv := by
    rintro ⟨vertex | child, heq⟩
    · change depth + 1 = age at heq
      omega
    · rfl
  right_inv := by rintro ⟨edge, address, heq⟩; rfl

/-- This equivalence acts on the actual generation vertices, not on an
independently introduced root law. -/
def interiorVertexAgeEquiv (rule : Rule) (depth age : ℕ) :
    {vertex : (rule.generation depth).network.InteriorVertex //
      rule.interiorVertexAge depth vertex = age} ≃ rule.BirthAgeFiber depth age where
  toFun vertex := ⟨rule.generationInteriorAddressEquiv depth vertex.val, vertex.property⟩
  invFun address := ⟨(rule.generationInteriorAddressEquiv depth).symm address.val, by
    simpa only [interiorVertexAge, Equiv.apply_symm_apply] using address.property⟩
  left_inv vertex := Subtype.ext ((rule.generationInteriorAddressEquiv depth).symm_apply_apply _)
  right_inv address := Subtype.ext ((rule.generationInteriorAddressEquiv depth).apply_symm_apply _)

end
end Universality.Rule
