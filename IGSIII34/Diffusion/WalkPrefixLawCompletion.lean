import IGSIII34.Diffusion.WalkEnergyIncrementCompletion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology

variable {Vertex Edge : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]

theorem finiteDiscreteWalkLaw_prefix_probability_step_completion
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (time : ℕ) (history : (coordinate : Finset.Iic (time + 1)) → Vertex) :
    (finiteDiscreteWalkLaw endpoint positiveDegree initial).map (frestrictLe (π := fun _ : ℕ => Vertex) (time + 1)) {history} =
      (finiteDiscreteWalkLaw endpoint positiveDegree initial).map (frestrictLe (π := fun _ : ℕ => Vertex) time)
        {frestrictLe₂ (π := fun _ : ℕ => Vertex) (Nat.le_succ time) history} *
      ENNReal.ofReal (transitionKernel endpoint
        (history ⟨time, Finset.mem_Iic.mpr (Nat.le_succ time)⟩)
        (history ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩)) := by
  classical
  have joint :
      ((finiteDiscreteWalkLaw endpoint positiveDegree initial).map (frestrictLe (π := fun _ : ℕ => Vertex) time)) ⊗ₘ
        finiteWalkHistoryKernel endpoint positiveDegree time =
      (finiteDiscreteWalkLaw endpoint positiveDegree initial).map
        (fun path => (frestrictLe (π := fun _ : ℕ => Vertex) time path, path (time + 1))) :=
    Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
  have probability := congrArg (fun law => law
    (({frestrictLe₂ (π := fun _ : ℕ => Vertex) (Nat.le_succ time) history} : Set ((coordinate : Finset.Iic time) → Vertex)) ×ˢ
      {history ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩})) joint
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton,
    Measure.map_apply ((measurable_frestrictLe (X := fun _ : ℕ => Vertex) time).prodMk (measurable_pi_apply (time + 1)))
      ((measurableSet_singleton _).prod (measurableSet_singleton _))] at probability
  have preimageEquality :
      (fun path : ℕ → Vertex => (frestrictLe (π := fun _ : ℕ => Vertex) time path, path (time + 1))) ⁻¹'
        (({frestrictLe₂ (π := fun _ : ℕ => Vertex) (Nat.le_succ time) history} : Set ((coordinate : Finset.Iic time) → Vertex)) ×ˢ
          {history ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩}) =
      (frestrictLe (π := fun _ : ℕ => Vertex) (time + 1)) ⁻¹' {history} := by
    ext path
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff]
    constructor
    · rintro ⟨historyRestriction, last⟩
      funext coordinate
      by_cases early : coordinate.val ≤ time
      · have equality := congrFun historyRestriction ⟨coordinate.val, Finset.mem_Iic.mpr early⟩
        simpa only [frestrictLe_apply, frestrictLe₂_apply] using equality
      · have late : coordinate.val = time + 1 := by
          have bound := Finset.mem_Iic.mp coordinate.property
          omega
        have coordinateIdentity : coordinate = ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩ := Subtype.ext late
        simpa only [frestrictLe_apply, coordinateIdentity] using last
    · intro full
      constructor
      · funext coordinate
        have equality := congrFun full
          ⟨coordinate.val, Finset.mem_Iic.mpr ((Finset.mem_Iic.mp coordinate.property).trans (Nat.le_succ time))⟩
        simpa only [frestrictLe_apply, frestrictLe₂_apply] using equality
      · exact congrFun full ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩
  rw [preimageEquality, ← Measure.map_apply (measurable_frestrictLe (X := fun _ : ℕ => Vertex) (time + 1))
    (measurableSet_singleton history)] at probability
  have kernel : finiteWalkHistoryKernel endpoint positiveDegree time
      (frestrictLe₂ (π := fun _ : ℕ => Vertex) (Nat.le_succ time) history) {history ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩} =
      ENNReal.ofReal (transitionKernel endpoint
        (history ⟨time, Finset.mem_Iic.mpr (Nat.le_succ time)⟩)
        (history ⟨time + 1, Finset.mem_Iic.mpr le_rfl⟩)) := by
    exact finiteWalkKernel_singleton endpoint positiveDegree _ _
  rw [kernel] at probability
  exact probability.symm.trans (mul_comm _ _)

/-- Detailed balance extends from a single genuine graph edge to every
specified finite path, without assuming a reversible path law. -/
theorem finiteWalk_path_product_balance_completion [Nonempty Edge]
    (endpoint : Edge → Vertex × Vertex)
    (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (path : ℕ → Vertex) (time : ℕ) :
    degreeWeight endpoint (path 0) *
      (∏ index ∈ Finset.range time, transitionKernel endpoint (path index) (path (index + 1))) =
    degreeWeight endpoint (path time) *
      (∏ index ∈ Finset.range time, transitionKernel endpoint (path (index + 1)) (path index)) := by
  induction time with
  | zero => simp
  | succ time induction =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, ← mul_assoc, induction]
    calc
      _ = (degreeWeight endpoint (path time) * transitionKernel endpoint (path time) (path (time + 1))) *
          (∏ index ∈ Finset.range time, transitionKernel endpoint (path (index + 1)) (path index)) := by ring
      _ = _ := by rw [detailed_balance endpoint positiveDegree]; ring

end
end IGSIII34.Diffusion
