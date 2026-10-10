import Universality.Graph.GenerationInternalNeighborhood
import Universality.Graph.BirthAgeFiber

namespace Universality.Rule
noncomputable section
set_option backward.isDefEq.respectTransparency false
open FiniteNetwork
open scoped BigOperators

def generationCellInterior (rule : Rule) (depth : ℕ) (edge : Fin rule.edges)
    (vertex : (rule.generation depth).network.InteriorVertex) :
    (rule.generation (depth + 1)).network.InteriorVertex :=
  ⟨(rule.generationCellEmbedding depth edge).vertex vertex.val,
    rule.generationCellEmbedding_internal depth edge vertex⟩

theorem generationCellInterior_eq (rule : Rule) (depth : ℕ) (edge : Fin rule.edges)
    (vertex : (rule.generation depth).network.InteriorVertex) :
    rule.generationCellInterior depth edge vertex =
      (rule.generationTopDecomposition depth).interiorEquiv.symm
        (rule.network.substitutionInteriorEquiv (rule.generation depth).network
          (Sum.inr (edge, vertex))) := by
  apply Subtype.ext
  change (rule.generationTopDecomposition depth).vertex.symm
    (Fintype.equivFin (rule.network.SubstitutionVertex (rule.generation depth).network)
      (rule.network.cellVertex (rule.generation depth).network edge vertex.val)) =
    (rule.generationTopDecomposition depth).vertex.symm
      (Fintype.equivFin (rule.network.SubstitutionVertex (rule.generation depth).network)
        (Sum.inr (edge, vertex)))
  rw [rule.network.cellVertex_eq_interior (rule.generation depth).network edge vertex]

/-- Adding an ancestral edge in the actual cell tower agrees exactly with
adding the corresponding symbol to the actual vertex's birth address. -/
theorem generationInteriorAddressEquiv_cell (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (vertex : (rule.generation depth).network.InteriorVertex) :
    rule.generationInteriorAddressEquiv (depth + 1)
      (rule.generationCellInterior depth edge vertex) =
        Sum.inr (edge, rule.generationInteriorAddressEquiv depth vertex) := by
  rw [rule.generationCellInterior_eq]
  simp only [generationInteriorAddressEquiv, Equiv.trans_apply, Equiv.apply_symm_apply,
    Equiv.symm_apply_apply]
  rfl

theorem interiorVertexAge_cell (rule : Rule) (depth : ℕ)
    (edge : Fin rule.edges) (vertex : (rule.generation depth).network.InteriorVertex) :
    rule.interiorVertexAge (depth + 1) (rule.generationCellInterior depth edge vertex) =
      rule.interiorVertexAge depth vertex := by
  simp only [interiorVertexAge, rule.generationInteriorAddressEquiv_cell, BirthAddress.age]

def interiorAgeFiberChildEquiv (rule : Rule) (depth age : ℕ) (hage : age ≤ depth) :
    {vertex : (rule.generation (depth + 1)).network.InteriorVertex //
      rule.interiorVertexAge (depth + 1) vertex = age} ≃
        Fin rule.edges × {vertex : (rule.generation depth).network.InteriorVertex //
          rule.interiorVertexAge depth vertex = age} :=
  (rule.interiorVertexAgeEquiv (depth + 1) age).trans
    ((rule.birthAgeFiberChildEquiv depth age hage).trans
      (Equiv.prodCongr (Equiv.refl _) (rule.interiorVertexAgeEquiv depth age).symm))

theorem interiorAgeFiberChildEquiv_symm (rule : Rule) (depth age : ℕ) (hage : age ≤ depth)
    (edge : Fin rule.edges)
    (vertex : {vertex : (rule.generation depth).network.InteriorVertex //
      rule.interiorVertexAge depth vertex = age}) :
    ((rule.interiorAgeFiberChildEquiv depth age hage).symm (edge, vertex)).val =
      rule.generationCellInterior depth edge vertex.val := by
  apply (rule.generationInteriorAddressEquiv (depth + 1)).injective
  change (rule.generationInteriorAddressEquiv (depth + 1))
    ((rule.generationInteriorAddressEquiv (depth + 1)).symm
      (((rule.birthAgeFiberChildEquiv depth age hage).symm
        (edge, rule.interiorVertexAgeEquiv depth age vertex)).val)) = _
  rw [Equiv.apply_symm_apply, rule.generationInteriorAddressEquiv_cell]
  rfl

/-- Exact disintegration of the actual finite-root age fibre into one freely
chosen ancestral edge and the previous generation's age fibre. -/
theorem sum_interiorVertexAge_succ (rule : Rule) (depth age : ℕ) (hage : age ≤ depth)
    (function : (rule.generation (depth + 1)).network.InteriorVertex → ℝ) :
    (∑ vertex : {vertex : (rule.generation (depth + 1)).network.InteriorVertex //
      rule.interiorVertexAge (depth + 1) vertex = age}, function vertex.val) =
      ∑ edge : Fin rule.edges,
        ∑ vertex : {vertex : (rule.generation depth).network.InteriorVertex //
          rule.interiorVertexAge depth vertex = age},
            function (rule.generationCellInterior depth edge vertex.val) := by
  classical
  rw [← (rule.interiorAgeFiberChildEquiv depth age hage).symm.sum_comp
    (fun vertex => function vertex.val), Fintype.sum_prod_type]
  simp only [rule.interiorAgeFiberChildEquiv_symm]

/-- The root of a tower of fixed age is a genuine oldest interior vertex of
its initial generation, chosen through the proved finite-age equivalence. -/
def ancestralRootInterior (rule : Rule) (age : ℕ) (seed : rule.network.InteriorVertex) :
    (rule.generation age).network.InteriorVertex :=
  ((rule.interiorVertexAgeEquiv age age).symm
    ((rule.birthAgeFiberSelfEquiv age).symm seed)).val

theorem ancestralRootInterior_age (rule : Rule) (age : ℕ) (seed : rule.network.InteriorVertex) :
    rule.interiorVertexAge age (rule.ancestralRootInterior age seed) = age :=
  ((rule.interiorVertexAgeEquiv age age).symm
    ((rule.birthAgeFiberSelfEquiv age).symm seed)).property

end
end Universality.Rule
