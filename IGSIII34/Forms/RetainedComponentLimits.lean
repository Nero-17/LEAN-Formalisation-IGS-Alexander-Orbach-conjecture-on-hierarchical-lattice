import IGSIII34.Forms.RetainedWordScaling
import IGSIII34.ResistanceLimit.StationarySelectedMonotonicity

set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Forms
noncomputable section
open Universality Universality.FiniteNetwork IGSIII34.Percolation IGSIII34.ResistanceLimit
open IGSIII.Chemical.Substitution IGSIII.Geometry
open scoped BigOperators

theorem finitePotential_persistent (rule : Rule)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (restriction : ∀ depth vertex, potentials (depth + 1) (rule.generationOldVertex depth vertex) = potentials depth vertex)
    (first last : ℕ) (bound : first ≤ last) (vertex : Fin (rule.generation first).vertices) :
    potentials last (persistentVertexEmbedding rule first last bound vertex) = potentials first vertex := by
  induction last, bound using Nat.le_induction with
  | base => simp only [persistentVertexEmbedding, Universality.Geometry.IsometricSequence.transition,
      Function.Embedding.coeFn_mk, Nat.leRecOn_self]
  | succ last bound previous =>
    rw [← persistentVertexEmbedding_trans rule first last (last + 1) bound (Nat.le_succ last),
      persistentVertexEmbedding_next, restriction]
    exact previous

theorem componentWordPotential_restriction (rule : Rule)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (restriction : ∀ depth vertex, potentials (depth + 1) (rule.generationOldVertex depth vertex) = potentials depth vertex)
    (age : ℕ) (word : Fin age → Fin rule.edges) (fine : ℕ)
    (vertex : Fin (rule.generation fine).vertices) :
    potentials ((fine + 1) + age)
        ((generationComponentWordEmbedding rule (fine + 1) age word).vertex (rule.generationOldVertex fine vertex)) =
      potentials (fine + age) ((generationComponentWordEmbedding rule fine age word).vertex vertex) := by
  have identity := generationComponentWordEmbedding_persistent rule fine (fine + 1) (Nat.le_succ fine) age word vertex
  have placed := congrArg (potentials ((fine + 1) + age)) identity
  rw [persistentVertexEmbedding_next] at placed
  have globalStep : potentials ((fine + 1) + age)
      (persistentVertexEmbedding rule (fine + age) ((fine + 1) + age) (by omega)
        ((generationComponentWordEmbedding rule fine age word).vertex vertex)) =
      potentials (fine + age) ((generationComponentWordEmbedding rule fine age word).vertex vertex) := by
    exact finitePotential_persistent rule potentials restriction (fine + age) ((fine + 1) + age) (by omega) _
  exact placed.symm.trans globalStep

variable (rule : Rule) (marks : (List (Fin rule.edges) × Bool) → Configuration rule.edges)
    (crossing : ∀ address opened, rule.network.crosses (marks (address, opened)) = opened)
    (field : List (Fin rule.edges) → ℝ) (growth : ℝ)
    (growthPositive : 0 < growth) (fieldPositive : ∀ address, 0 < field address)
    (stationary : ∀ address, electricalCell rule.network (marks (address, true))
      (fun edge => field (address ++ [edge])) = growth * field address)
    (potentials : ∀ depth, Fin (rule.generation depth).vertices → ℝ)
    (restriction : ∀ depth vertex, potentials (depth + 1) (rule.generationOldVertex depth vertex) = potentials depth vertex)

include growthPositive fieldPositive stationary restriction

theorem stationary_retainedWordTraceEnergy_monotone (age : ℕ) (word : Fin age → (Fin rule.edges × Bool)) :
    Monotone (fun fine => retainedWordTraceEnergy rule marks crossing fine age
      (fun edge => stationaryGenerationResistance rule field growth (fine + age) [] edge.val)
      (potentials (fine + age)) word) := by
  have localMonotone := stationary_selectedComponentTraceEnergy_monotone rule marks field growth growthPositive
    fieldPositive crossing stationary (List.ofFn word)
    (fun fine => potentials (fine + age) ∘ (generationComponentWordEmbedding rule fine age (fun index => (word index).1)).vertex)
    (componentWordPotential_restriction rule potentials restriction age (fun index => (word index).1))
  intro first last bound
  dsimp only
  rw [retainedWordTraceEnergy_stationary_scaling, retainedWordTraceEnergy_stationary_scaling]
  exact mul_le_mul_of_nonneg_left (localMonotone bound) (pow_pos growthPositive age).le

/-- The full finite-energy form decomposes over the genuine retained words,
with separately selected sides and the original global normalization. -/
theorem stationary_retained_component_energy_decomposition (age : ℕ)
    (finite : BddAbove (Set.range (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
      (fun edge => stationaryGenerationResistance rule field growth depth [] edge.val) (potentials depth)))) :
    (⨆ depth, sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
      (fun edge => stationaryGenerationResistance rule field growth depth [] edge.val) (potentials depth)) =
      ∑ word : Fin age → (Fin rule.edges × Bool), ⨆ fine,
        retainedWordTraceEnergy rule marks crossing fine age
          (fun edge => stationaryGenerationResistance rule field growth (fine + age) [] edge.val)
          (potentials (fine + age)) word := by
  have totalMonotone : Monotone (fun depth => sourceComponentEnergy
      (network (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true))
      (fun edge => stationaryGenerationResistance rule field growth depth [] edge.val) (potentials depth)) := by
    apply monotone_nat_of_le_succ
    intro depth
    have comparison := stationary_generation_side_source_energy_le rule marks field growth growthPositive
      fieldPositive crossing stationary depth [] true true (potentials (depth + 1))
    simpa only [sideNetwork, if_true, restriction] using comparison
  exact (component_trace_supremum_decomposition _ _ age
    (fun word fine => retainedWordTraceEnergy_nonnegative rule marks crossing fine age _
      (fun edge => mul_pos (pow_pos (inv_pos.mpr growthPositive) _) (fieldPositive _)) _ word)
    (stationary_retainedWordTraceEnergy_monotone rule marks crossing field growth growthPositive fieldPositive stationary potentials restriction age)
    totalMonotone
    (fun fine => sourceComponentEnergy_eq_sum_retained_word_energy rule marks crossing fine age _ _)
    finite).2.1

end
end IGSIII34.Forms
