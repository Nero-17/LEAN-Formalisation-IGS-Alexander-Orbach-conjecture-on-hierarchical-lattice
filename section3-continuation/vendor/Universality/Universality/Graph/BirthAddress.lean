import Universality.Graph.InteriorDecomposition

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A concrete finite birth address. The left branch is an original outer
interior vertex; the right branch selects its containing child edge. -/
def BirthAddress (rule : Rule) : ℕ → Type
  | 0 => rule.network.InteriorVertex
  | n + 1 => rule.network.InteriorVertex ⊕ (Fin rule.edges × rule.BirthAddress n)

def generationInteriorAddressEquiv (rule : Rule) :
    (n : ℕ) → (rule.generation n).network.InteriorVertex ≃ rule.BirthAddress n
  | 0 => Equiv.refl _
  | n + 1 =>
    (rule.generationTopDecomposition n).interiorEquiv.trans
      ((rule.network.substitutionInteriorEquiv (rule.generation n).network).symm.trans
        (Equiv.sumCongr (Equiv.refl _)
          (Equiv.prodCongr (Equiv.refl _) (rule.generationInteriorAddressEquiv n))))

def BirthAddress.age (rule : Rule) : (n : ℕ) → rule.BirthAddress n → ℕ
  | 0, _ => 0
  | n + 1, .inl _ => n + 1
  | n + 1, .inr child => BirthAddress.age rule n child.2

theorem BirthAddress.age_le (rule : Rule) (n : ℕ) (address : rule.BirthAddress n) :
    BirthAddress.age rule n address ≤ n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    cases address with
    | inl old => exact le_rfl
    | inr child => exact (ih child.2).trans (Nat.le_succ n)

/-- The actual age of a finite interior vertex, obtained from the proved
decomposition rather than assigned by a desired limiting distribution. -/
def interiorVertexAge (rule : Rule) (n : ℕ) (v : (rule.generation n).network.InteriorVertex) : ℕ :=
  BirthAddress.age rule n (rule.generationInteriorAddressEquiv n v)

theorem interiorVertexAge_le (rule : Rule) (n : ℕ) (v : (rule.generation n).network.InteriorVertex) :
    rule.interiorVertexAge n v ≤ n := BirthAddress.age_le rule n _

end
end Universality.Rule

