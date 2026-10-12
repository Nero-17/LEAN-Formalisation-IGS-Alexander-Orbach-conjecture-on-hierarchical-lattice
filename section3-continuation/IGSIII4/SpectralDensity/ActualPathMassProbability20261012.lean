import IGSIII4.SpectralDensity.ActualPathMassCut20261012
import IGSIII4.SpectralDensity.ActualProbability20261012
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Data.Fin.Rev

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
attribute [local instance] Classical.propDecidable
open Universality Universality.FiniteNetwork
open scoped BigOperators

theorem selected_edges_probability {edges : ℕ} (probability : ℝ) (selected : Finset (Fin edges)) :
    expectation probability (fun configuration => if ∀ edge ∈ selected, configuration edge = true then 1 else 0) =
      probability ^ selected.card := by
  unfold expectation
  calc
    _ = ∑ configuration : Configuration edges,
        if ∀ edge, edge ∈ selected → configuration edge = true then
          (∏ edge, if configuration edge then probability else 1 - probability) else 0 := by
      apply Finset.sum_congr rfl
      intro configuration _
      by_cases allOpen : ∀ edge ∈ selected, configuration edge = true <;> simp [allOpen, bernoulliWeight]
    _ = ∏ edge : Fin edges, ∑ opened : Bool,
        if edge ∈ selected → opened = true then (if opened then probability else 1 - probability) else 0 :=
      by
        convert finite_product_event_all (fun (_ : Fin edges) (opened : Bool) => if opened then probability else 1 - probability)
          (fun edge opened => edge ∈ selected → opened = true) using 1
        · apply Finset.sum_congr rfl
          intro configuration _
          by_cases allOpen : ∀ edge ∈ selected, configuration edge = true <;> simp [allOpen]
        · apply Finset.prod_congr rfl
          intro edge _
          apply Finset.sum_congr rfl
          intro opened _
          by_cases event : edge ∈ selected → opened = true <;> simp [event]
    _ = ∏ edge : Fin edges, if edge ∈ selected then probability else 1 := by
      apply Finset.prod_congr rfl
      intro edge _
      by_cases membership : edge ∈ selected <;> simp [membership, Fintype.sum_bool]
    _ = _ := by rw [Finset.prod_ite]; simp

def pathEdgeIndex (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (edge : Fin (interior + 2)) : Fin (Fintype.card (Edge blocks paths interior)) :=
  Fintype.equivFin _ (.inr (block, path, edge))

theorem pathEdgeIndex_injective (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths) :
    Function.Injective (pathEdgeIndex blocks paths interior block path) := by
  intro first second equal
  have typed := (Fintype.equivFin (Edge blocks paths interior)).injective equal
  simpa only [Sum.inr.injEq, Prod.mk.injEq, true_and] using typed

theorem path_subset_probability (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (selected : Finset (Fin (interior + 2))) (probability : ℝ) :
    expectation probability (fun configuration : Configuration (Fintype.card (Edge blocks paths interior)) =>
      if ∀ edge ∈ selected, configuration (pathEdgeIndex blocks paths interior block path edge) = true then 1 else 0) =
        probability ^ selected.card := by
  have identity := selected_edges_probability probability (selected.image (pathEdgeIndex blocks paths interior block path))
  have eventRewrite (configuration : Configuration (Fintype.card (Edge blocks paths interior))) :
      (∀ actual ∈ selected.image (pathEdgeIndex blocks paths interior block path), configuration actual = true) ↔
        ∀ edge ∈ selected, configuration (pathEdgeIndex blocks paths interior block path edge) = true := by simp
  simp_rw [eventRewrite] at identity
  rwa [Finset.card_image_of_injective selected (pathEdgeIndex_injective blocks paths interior block path)] at identity

theorem path_end_event_probability_le (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (edge : Fin (interior + 2)) (probability : ℝ) (nonnegative : 0 ≤ probability) (atMostOne : probability ≤ 1) :
    expectation probability (fun configuration : Configuration (Fintype.card (Edge blocks paths interior)) =>
      if EdgeEndEvent blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge)) block path edge then 1 else 0) ≤
        probability ^ edge.val + probability ^ (interior + 2 - 1 - edge.val) := by
  have initialProbability := path_subset_probability blocks paths interior block path (Finset.Iio edge) probability
  have suffix := path_subset_probability blocks paths interior block path (Finset.Ioi edge) probability
  simp only [Fin.card_Iio, Fin.card_Ioi, Finset.mem_Iio, Finset.mem_Ioi, Fin.lt_def] at initialProbability suffix
  have pointwise (configuration : Configuration (Fintype.card (Edge blocks paths interior))) :
      (if EdgeEndEvent blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge)) block path edge then (1 : ℝ) else 0) ≤
        (if ∀ earlier : Fin (interior + 2), earlier.val < edge.val →
            configuration (pathEdgeIndex blocks paths interior block path earlier) = true then 1 else 0) +
          (if ∀ later : Fin (interior + 2), edge.val < later.val →
            configuration (pathEdgeIndex blocks paths interior block path later) = true then 1 else 0) := by
    unfold EdgeEndEvent pathEdgeIndex
    have indicatorUnion (first second : Prop) :
        (if first ∨ second then (1 : ℝ) else 0) ≤ (if first then 1 else 0) + (if second then 1 else 0) := by
      by_cases first <;> by_cases second <;> simp_all
    convert indicatorUnion
      (∀ earlier : Fin (interior + 2), earlier.val < edge.val →
        configuration (Fintype.equivFin _ (.inr (block, path, earlier))) = true)
      (∀ later : Fin (interior + 2), edge.val < later.val →
        configuration (Fintype.equivFin _ (.inr (block, path, later))) = true) using 1 <;> split_ifs <;> rfl

  have comparison := Finset.sum_le_sum (fun configuration (_ : configuration ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_left (pointwise configuration) (bernoulliWeight_nonneg nonnegative atMostOne configuration))
  change expectation probability _ ≤ expectation probability (fun configuration => _ + _) at comparison
  rw [expectation_add, initialProbability, suffix] at comparison
  exact comparison

theorem finite_geometric_sum_lt (length : ℕ) (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1) :
    (∑ edge : Fin length, probability ^ edge.val) < 1 / (1 - probability) := by
  have geometric := geom_sum_mul_neg probability length
  rw [← Fin.sum_univ_eq_sum_range] at geometric
  apply (lt_div_iff₀ (by linarith : 0 < 1 - probability)).mpr
  nlinarith [pow_pos positive length]

theorem path_end_probability_sum_lt (blocks paths interior : ℕ) (block : Fin blocks) (path : Fin paths)
    (probability : ℝ) (positive : 0 < probability) (belowOne : probability < 1) :
    (∑ edge : Fin (interior + 2), expectation probability
      (fun configuration : Configuration (Fintype.card (Edge blocks paths interior)) =>
        if EdgeEndEvent blocks paths interior (fun edge => configuration (Fintype.equivFin _ edge)) block path edge then 1 else 0)) <
      2 / (1 - probability) := by
  have comparison := Finset.sum_le_sum (fun edge (_ : edge ∈ Finset.univ) =>
    path_end_event_probability_le blocks paths interior block path edge probability positive.le belowOne.le)
  rw [Finset.sum_add_distrib] at comparison
  have reverseSum : (∑ edge : Fin (interior + 2), probability ^ (interior + 2 - 1 - edge.val)) =
      ∑ edge : Fin (interior + 2), probability ^ edge.val := by
    calc
      _ = ∑ edge : Fin (interior + 2), probability ^ (Fin.revPerm edge).val := by
        apply Finset.sum_congr rfl
        intro edge _
        congr 1
        simp only [Fin.revPerm_apply, Fin.val_rev]
        omega
      _ = _ := Equiv.sum_comp Fin.revPerm (fun edge : Fin (interior + 2) => probability ^ edge.val)
  rw [reverseSum] at comparison
  have geometric := finite_geometric_sum_lt (interior + 2) probability positive belowOne
  have twoDivision : 2 / (1 - probability) = 2 * (1 / (1 - probability)) := by ring
  rw [twoDivision]
  linarith

end
end IGSIII4.SpectralDensity.ActualFamily
