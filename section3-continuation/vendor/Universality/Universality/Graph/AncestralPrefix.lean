import Universality.Graph.AncestralInterior
import Universality.Graph.NetworkTower
import Mathlib.Data.Fin.Tuple.Basic

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A base interior vertex and a finite ancestral prefix parametrize exactly
the actual vertices of that age in the corresponding finite generation. -/
def ancestralPrefixEquiv (rule : Rule) (age : ℕ) : (n : ℕ) →
    (rule.network.InteriorVertex × (Fin n → Fin rule.edges)) ≃
      {vertex : (rule.generation (age + n)).network.InteriorVertex //
        rule.interiorVertexAge (age + n) vertex = age}
  | 0 => (Equiv.prodUnique _ _).trans
      ((rule.birthAgeFiberSelfEquiv age).symm.trans (rule.interiorVertexAgeEquiv age age).symm)
  | n + 1 => by
    let split : (rule.network.InteriorVertex × (Fin (n + 1) → Fin rule.edges)) ≃
        Fin rule.edges × (rule.network.InteriorVertex × (Fin n → Fin rule.edges)) :=
      (Equiv.prodCongr (Equiv.refl _) (Fin.snocEquiv (fun _ => Fin rule.edges)).symm).trans
        ((Equiv.prodAssoc _ _ _).symm.trans
          ((Equiv.prodCongr (Equiv.prodComm _ _) (Equiv.refl _)).trans (Equiv.prodAssoc _ _ _)))
    exact (split.trans (Equiv.prodCongr (Equiv.refl _) (rule.ancestralPrefixEquiv age n))).trans
      (rule.interiorAgeFiberChildEquiv (age + n) age (by omega)).symm

theorem ancestralPrefixEquiv_zero (rule : Rule) (age : ℕ)
    (seed : rule.network.InteriorVertex) (word : Fin 0 → Fin rule.edges) :
    (rule.ancestralPrefixEquiv age 0 (seed, word)).val = rule.ancestralRootInterior age seed := by
  rfl

theorem ancestralPrefixEquiv_succ (rule : Rule) (age n : ℕ)
    (seed : rule.network.InteriorVertex) (word : Fin (n + 1) → Fin rule.edges) :
    (rule.ancestralPrefixEquiv age (n + 1) (seed, word)).val =
      rule.generationCellInterior (age + n) (word (Fin.last n))
        (rule.ancestralPrefixEquiv age n (seed, Fin.init word)).val := by
  exact rule.interiorAgeFiberChildEquiv_symm (age + n) age (by omega)
    (word (Fin.last n)) (rule.ancestralPrefixEquiv age n (seed, Fin.init word))

/-- The finite-prefix parametrization follows the physical tower embeddings,
not just a cardinality-preserving abstract labelling. -/
theorem ancestralPrefixEquiv_towerRoot (rule : Rule) (age n : ℕ)
    (seed : rule.network.InteriorVertex) (address : ℕ → Fin rule.edges) :
    (rule.ancestralPrefixEquiv age n (seed, fun i => address i.val)).val.val =
      (rule.ancestralTower age address).vertexMap 0 n (Nat.zero_le n)
        (rule.ancestralRootInterior age seed).val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [rule.ancestralPrefixEquiv_succ]
    change (rule.generationCellEmbedding (age + n) (address n)).vertex
      (rule.ancestralPrefixEquiv age n (seed, fun i => address i.val)).val.val = _
    rw [ih]
    simp only [NetworkTower.vertexMap, Nat.leRecOn_succ (Nat.zero_le n)]
    rfl

end
end Universality.Rule
