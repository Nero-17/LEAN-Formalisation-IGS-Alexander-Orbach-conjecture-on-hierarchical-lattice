import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! A law on the countable skeleton is uniquely determined by its initial
marginal and regular conditional successor kernels. This gives equality
of every finite-dimensional law, without presupposing process existence. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Spectral
noncomputable section
open MeasureTheory ProbabilityTheory Preorder
open scoped ProbabilityTheory
variable {Space : Type*} [MeasurableSpace Space] [StandardBorelSpace Space] [Nonempty Space]

def markovPrefixAppendCompletion20261011 (index : ℕ)
    (pair : (Finset.Iic index → Space) × Space) : Finset.Iic (index+1) → Space :=
  fun coordinate => if below : coordinate.val ≤ index then
    pair.1 ⟨coordinate.val, Finset.mem_Iic.mpr below⟩ else pair.2

theorem markovPrefixAppend_measurable_completion20261011 (index : ℕ) :
    Measurable (markovPrefixAppendCompletion20261011 (Space := Space) index) := by
  apply measurable_pi_lambda
  intro coordinate
  by_cases below : coordinate.val ≤ index
  · simp only [markovPrefixAppendCompletion20261011, dif_pos below]
    exact (measurable_pi_apply (⟨coordinate.val, Finset.mem_Iic.mpr below⟩ : Finset.Iic index)).comp measurable_fst
  · simp only [markovPrefixAppendCompletion20261011, dif_neg below]
    exact measurable_snd

theorem countable_law_eq_of_initial_and_conditional_kernels_completion20261011
    (first second : Measure (ℕ → Space)) [IsProbabilityMeasure first] [IsProbabilityMeasure second]
    (steps : (index : ℕ) → Kernel (Finset.Iic index → Space) Space)
    [∀ index, IsFiniteKernel (steps index)]
    (initial : first.map (fun path => path 0) = second.map (fun path => path 0))
    (firstConditional : ∀ index, condDistrib (fun path : ℕ → Space => path (index+1))
      (frestrictLe (π := fun _ : ℕ => Space) index) first =ᵐ[first.map (frestrictLe (π := fun _ : ℕ => Space) index)] steps index)
    (secondConditional : ∀ index, condDistrib (fun path : ℕ → Space => path (index+1))
      (frestrictLe (π := fun _ : ℕ => Space) index) second =ᵐ[second.map (frestrictLe (π := fun _ : ℕ => Space) index)] steps index) :
    first = second := by
  have prefixes : ∀ index, first.map (frestrictLe (π := fun _ : ℕ => Space) index) = second.map (frestrictLe (π := fun _ : ℕ => Space) index) := by
    intro index
    induction index with
    | zero =>
      have zeroRestriction : (frestrictLe (π := fun _ : ℕ => Space) 0) =
          (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => Space)).symm ∘ (fun path : ℕ → Space => path 0) := by
        funext path coordinate
        have coordinateZero : coordinate.val = 0 := by
          have := Finset.mem_Iic.mp coordinate.property
          omega
        have coordinateEq : coordinate = (⟨0, Finset.mem_Iic.mpr le_rfl⟩ : Finset.Iic 0) := Subtype.ext coordinateZero
        rw [coordinateEq]
        rfl
      rw [zeroRestriction, ← Measure.map_map (MeasurableEquiv.piUnique _).symm.measurable (measurable_pi_apply 0),
        ← Measure.map_map (MeasurableEquiv.piUnique _).symm.measurable (measurable_pi_apply 0), initial]
    | succ index inductionHypothesis =>
      have firstJoint := (condDistrib_ae_eq_iff_measure_eq_compProd (μ := first)
        (frestrictLe (π := fun _ : ℕ => Space) index) (measurable_pi_apply (index+1)).aemeasurable (steps index)).mp (firstConditional index)
      have secondJoint := (condDistrib_ae_eq_iff_measure_eq_compProd (μ := second)
        (frestrictLe (π := fun _ : ℕ => Space) index) (measurable_pi_apply (index+1)).aemeasurable (steps index)).mp (secondConditional index)
      have appendRestriction : markovPrefixAppendCompletion20261011 (Space := Space) index ∘
          (fun path : ℕ → Space => (frestrictLe (π := fun _ : ℕ => Space) index path, path (index+1))) = frestrictLe (π := fun _ => Space) (index+1) := by
        funext path coordinate
        dsimp only [Function.comp_apply, markovPrefixAppendCompletion20261011]
        split_ifs with below
        · rfl
        · have coordinateLast : coordinate.val = index+1 := by
            have := Finset.mem_Iic.mp coordinate.property
            omega
          simp only [coordinateLast, frestrictLe_apply]
      rw [← appendRestriction, ← Measure.map_map (markovPrefixAppend_measurable_completion20261011 index)
        ((measurable_frestrictLe index).prodMk (measurable_pi_apply (index+1))),
        ← Measure.map_map (markovPrefixAppend_measurable_completion20261011 index)
          ((measurable_frestrictLe index).prodMk (measurable_pi_apply (index+1))), firstJoint, secondJoint, inductionHypothesis]
  letI : ∀ index : ℕ, IsProbabilityMeasure (first.map (frestrictLe (π := fun _ : ℕ => Space) index)) := fun index =>
    Measure.isProbabilityMeasure_map (measurable_frestrictLe index).aemeasurable
  letI : ∀ index : ℕ, IsFiniteMeasure (first.map (frestrictLe (π := fun _ : ℕ => Space) index)) := fun index => inferInstance
  letI : ∀ indices : Finset ℕ, IsFiniteMeasure
      (inducedFamily (X := fun _ : ℕ => Space)
        (fun index => first.map (frestrictLe (π := fun _ : ℕ => Space) index)) indices) := fun indices => by
    unfold inducedFamily
    infer_instance
  have projective : IsProjectiveMeasureFamily (α := fun _ : ℕ => Space) (inducedFamily (X := fun _ : ℕ => Space) (fun index => first.map (frestrictLe (π := fun _ : ℕ => Space) index))) := by
    apply isProjectiveMeasureFamily_inducedFamily
    intro lower upper below
    rw [Measure.map_map (measurable_frestrictLe₂ below) (measurable_frestrictLe upper)]
    rfl
  have firstLimit : IsProjectiveLimit (α := fun _ : ℕ => Space) first (inducedFamily (X := fun _ : ℕ => Space) (fun index => first.map (frestrictLe (π := fun _ : ℕ => Space) index))) := by
    apply (isProjectiveLimit_nat_iff projective first).mpr
    intro index
    rw [inducedFamily_Iic]
  have secondLimit : IsProjectiveLimit (α := fun _ : ℕ => Space) second (inducedFamily (X := fun _ : ℕ => Space) (fun index => first.map (frestrictLe (π := fun _ : ℕ => Space) index))) := by
    apply (isProjectiveLimit_nat_iff projective second).mpr
    intro index
    rw [inducedFamily_Iic, prefixes index]
  exact firstLimit.unique secondLimit

end
end IGSIII34.Spectral





