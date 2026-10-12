import IGSIII4.SpectralDensity.ActualMomentFiniteLaw
import IGSIII4.SpectralDensity.ActualProbability
import IGSIII4.SpectralDensity.ActualMomentLongLaw

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open Universality Universality.FiniteNetwork IGSIII34.Probability IGSIII34.Percolation
attribute [local instance] Classical.propDecidable

abbrev CircuitInput (blocks paths interior : ℕ) (Outcome : Type*) :=
  (Fin 4 → Outcome) × (Fin blocks → Fin paths → Fin (interior + 2) → Outcome)

def inputEquiv (blocks paths interior : ℕ) (Outcome : Type*) :
    (Fin (Fintype.card (Edge blocks paths interior)) → Outcome) ≃ CircuitInput blocks paths interior Outcome where
  toFun input := (fun edge => input (Fintype.equivFin _ (.inl edge)),
    fun block path edge => input (Fintype.equivFin _ (.inr (block, path, edge))))
  invFun input edge := match (Fintype.equivFin (Edge blocks paths interior)).symm edge with
    | .inl outer => input.1 outer
    | .inr (block, path, inner) => input.2 block path inner
  left_inv input := by
    funext edge
    have identity := congrArg input ((Fintype.equivFin (Edge blocks paths interior)).apply_symm_apply edge)
    cases equal : (Fintype.equivFin (Edge blocks paths interior)).symm edge with
    | inl outer => simpa only [equal] using identity
    | inr triple => rcases triple with ⟨block, path, inner⟩; simpa only [equal] using identity
  right_inv input := by
    rcases input with ⟨outer, inner⟩
    apply Prod.ext
    · funext edge; simp
    · funext block path edge; simp

def splitTyped {blocks paths interior : ℕ} {Outcome : Type*}
    (input : CircuitInput blocks paths interior Outcome) : Edge blocks paths interior → Outcome
  | .inl outer => input.1 outer
  | .inr (block, path, inner) => input.2 block path inner

theorem input_weight {Outcome : Type*} [Fintype Outcome]
    (blocks paths interior : ℕ) (weight : Outcome → ℝ)
    (input : Fin (Fintype.card (Edge blocks paths interior)) → Outcome) :
    productWeight weight input = productWeight weight ((inputEquiv blocks paths interior Outcome) input).1 *
      productWeight (blockProductWeight weight) ((inputEquiv blocks paths interior Outcome) input).2 := by
  unfold productWeight blockProductWeight
  calc
    _ = ∏ edge : Edge blocks paths interior, weight (input (Fintype.equivFin _ edge)) :=
      ((Fintype.equivFin (Edge blocks paths interior)).prod_comp _).symm
    _ = _ := by
      rw [Fintype.prod_sum_type]
      simp only [Fintype.prod_prod_type, inputEquiv, Equiv.coe_fn_mk, productWeight]

theorem input_mean_transfer {Outcome : Type*} [Fintype Outcome]
    (blocks paths interior : ℕ) (weight : Outcome → ℝ)
    (observable : CircuitInput blocks paths interior Outcome → ℝ) :
    finiteMean (productWeight weight) (fun input => observable (inputEquiv blocks paths interior Outcome input)) =
      finiteMean (productWeight weight) (fun outer : Fin 4 → Outcome =>
        finiteMean (productWeight (blockProductWeight weight)) (fun inner : Fin blocks → Fin paths → Fin (interior + 2) → Outcome =>
          observable (outer, inner))) := by
  unfold finiteMean
  simp_rw [input_weight blocks paths interior weight]
  rw [(inputEquiv blocks paths interior Outcome).sum_comp (fun input =>
    productWeight weight input.1 * productWeight (blockProductWeight weight) input.2 * observable input)]
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum, mul_assoc]

def circuitObservable {Outcome : Type*} (blocks paths interior : ℕ)
    (configuration : CircuitConfiguration blocks paths interior)
    (response : Outcome → ℝ) (observable : ℝ → ℝ) (input : CircuitInput blocks paths interior Outcome) : ℝ :=
  observable (circuitVoltage (splitTyped configuration) (fun edge => response (splitTyped input edge)))

/-- Exact coarse and fine product disintegration of the actual weighted electrical cell. -/
theorem weightedCellObservable_split {Outcome : Type*} [Fintype Outcome]
    (blocks paths interior : ℕ) (probability : ℝ)
    (fixedPoint : (network blocks paths interior).reliability probability = probability)
    (weight response : Outcome → ℝ) (positive : ∀ outcome, 0 < response outcome) (observable : ℝ → ℝ) :
    weightedCellObservable blocks paths interior probability weight response observable =
      (∑ inner : Fin blocks → Fin paths → Configuration (interior + 2),
        chainWeight blocks paths (interior + 2) probability inner *
          Universality.FiniteNetwork.expectation probability (fun outer =>
            if outerCrossing (chainCrossing blocks paths (interior + 2) inner) outer then
              finiteMean (productWeight weight) (fun fineOuter : Fin 4 → Outcome =>
                finiteMean (productWeight (blockProductWeight weight))
                  (fun fineInner : Fin blocks → Fin paths → Fin (interior + 2) → Outcome =>
                    circuitObservable blocks paths interior (outer, inner) response observable (fineOuter, fineInner)))
            else 0)) / probability := by
  let average : CircuitConfiguration blocks paths interior → ℝ := fun configuration =>
    if outerCrossing (chainCrossing blocks paths (interior + 2) configuration.2) configuration.1 then
      finiteMean (productWeight weight) (fun fineOuter : Fin 4 → Outcome =>
        finiteMean (productWeight (blockProductWeight weight))
          (fun fineInner : Fin blocks → Fin paths → Fin (interior + 2) → Outcome =>
            circuitObservable blocks paths interior configuration response observable (fineOuter, fineInner)))
    else 0
  have summand (configuration : Configuration (Fintype.card (Edge blocks paths interior))) :
      (network blocks paths interior).conditionalCellWeight probability true configuration *
        finiteMean (productWeight weight) (fun input => observable (electricalCell (network blocks paths interior)
          configuration (fun edge => response (input edge)))) =
      (bernoulliWeight probability configuration * average (configurationEquiv blocks paths interior configuration)) / probability := by
    by_cases crossing : (network blocks paths interior).crosses configuration = true
    · have circuitCross := (configuration_crossing blocks paths interior configuration).mp crossing
      simp only [conditionalCellWeight, crossing, ↓reduceIte, fixedPoint, average, circuitCross]
      have fineIdentity : finiteMean (productWeight weight) (fun input => observable (electricalCell (network blocks paths interior)
          configuration (fun edge => response (input edge)))) =
          finiteMean (productWeight weight) (fun outer : Fin 4 → Outcome =>
            finiteMean (productWeight (blockProductWeight weight)) (fun inner : Fin blocks → Fin paths → Fin (interior + 2) → Outcome =>
              circuitObservable blocks paths interior (configurationEquiv blocks paths interior configuration) response observable (outer, inner))) := by
        rw [← input_mean_transfer blocks paths interior weight]
        apply congrArg (finiteMean (productWeight weight))
        funext input
        rw [electricalCell_eq_circuitVoltage blocks paths interior configuration _ (fun edge => positive _) crossing]
        rfl
      rw [fineIdentity]
      ring
    · have circuitFailed : ¬outerCrossing (chainCrossing blocks paths (interior + 2)
          (configurationEquiv blocks paths interior configuration).2)
          (configurationEquiv blocks paths interior configuration).1 :=
        fun h => crossing ((configuration_crossing blocks paths interior configuration).mpr h)
      simp [conditionalCellWeight, crossing, fixedPoint, average, circuitFailed]
  change (∑ configuration : Configuration (Fintype.card (Edge blocks paths interior)),
    (network blocks paths interior).conditionalCellWeight probability true configuration *
      finiteMean (productWeight weight) (fun input => observable (electricalCell (network blocks paths interior)
        configuration (fun edge => response (input edge))))) = _
  simp_rw [summand]
  rw [← Finset.sum_div, configuration_sum_transfer blocks paths interior probability average]

end
end IGSIII4.SpectralDensity.ActualFamily
