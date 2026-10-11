import Universality.Graph.Rule
import Mathlib.Combinatorics.Quiver.Basic

namespace Universality.Geometry
noncomputable section
open scoped BigOperators

/-- Finite coloured two-terminal substitution rules. A draw chooses a whole
rule, so sibling incidences and child colours may be dependent. -/
structure RuleFamilies (Colour : Type*) [Fintype Colour] where
  Choice : Colour → Type
  finiteChoice : ∀ i, Fintype (Choice i)
  rule : ∀ i, Choice i → Rule
  childColour : ∀ i (choice : Choice i), Fin (rule i choice).edges → Colour
  probability : ∀ i, Choice i → ℝ
  probability_nonneg : ∀ i choice, 0 ≤ probability i choice
  probability_sum : ∀ i, @Finset.sum (Choice i) ℝ _ (finiteChoice i).elems (probability i) = 1

namespace RuleFamilies
variable {Colour : Type*} [Fintype Colour] (families : RuleFamilies Colour)

instance (i : Colour) : Fintype (families.Choice i) := families.finiteChoice i

/-- Every construction-graph edge retains its parent rule label. Distinct
rules with identical underlying graphs are not silently identified. -/
def Transition (i j : Colour) :=
  (choice : families.Choice i) × {e : Fin (families.rule i choice).edges //
    families.childColour i choice e = j}

@[reducible] def constructionQuiver : Quiver Colour where
  Hom := families.Transition

def outgoingFamily (i : Colour) (choice : families.Choice i)
    (e : Fin (families.rule i choice).edges) :
    (j : Colour) × families.Transition i j :=
  ⟨families.childColour i choice e, choice, e, rfl⟩

theorem outgoingFamily_target (i : Colour) (choice : families.Choice i)
    (e : Fin (families.rule i choice).edges) :
    (families.outgoingFamily i choice e).1 = families.childColour i choice e := rfl

theorem outgoingFamily_rule (i : Colour) (choice : families.Choice i)
    (e : Fin (families.rule i choice).edges) :
    (families.outgoingFamily i choice e).2.1 = choice := rfl

/-- Independent selections are made between cells. Each selection is a
single rule choice, not a product of independent choices for its children. -/
def finiteChoiceWeight {Cell : Type*} [Fintype Cell] (colour : Cell → Colour)
    (choices : (cell : Cell) → families.Choice (colour cell)) : ℝ :=
  ∏ cell, families.probability (colour cell) (choices cell)

theorem finiteChoiceWeight_nonneg {Cell : Type*} [Fintype Cell] (colour : Cell → Colour)
    (choices : (cell : Cell) → families.Choice (colour cell)) :
    0 ≤ families.finiteChoiceWeight colour choices := by
  apply Finset.prod_nonneg
  intro cell _
  exact families.probability_nonneg _ _

theorem sum_finiteChoiceWeight {Cell : Type*} [Fintype Cell] [DecidableEq Cell] (colour : Cell → Colour) :
    ∑ choices, families.finiteChoiceWeight colour choices = 1 := by
  unfold finiteChoiceWeight
  rw [← Fintype.prod_sum (fun cell choice => families.probability (colour cell) choice)]
  simp only [show ∀ i, (∑ choice, families.probability i choice) = 1 from families.probability_sum]
  simp

end RuleFamilies
end
end Universality.Geometry
