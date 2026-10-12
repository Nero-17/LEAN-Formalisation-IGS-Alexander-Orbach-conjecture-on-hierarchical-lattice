import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Kernel.CondDistrib

set_option autoImplicit false
set_option maxHeartbeats 2400000
namespace IGSIII34.Diffusion
noncomputable section
open MeasureTheory Filter Set
open scoped _root_.Topology ProbabilityTheory
variable {Outcome Space : Type*} [MeasurableSpace Outcome]
  [TopologicalSpace Space] [TopologicalSpace.MetrizableSpace Space] [MeasurableSpace Space] [BorelSpace Space]

theorem finiteHistory_comap_eq_natural_completion
    (history : ℕ → Outcome → Space) (historyStrong : ∀ index, StronglyMeasurable (history index)) (count : ℕ) :
    MeasurableSpace.comap (fun outcome => fun coordinate : Fin (count+1) => history coordinate.val outcome) inferInstance =
      Filtration.natural history historyStrong count := by
  rw [MeasurableSpace.comap_process_pi]
  change (⨆ coordinate : Fin (count+1), MeasurableSpace.comap (history coordinate.val) inferInstance) =
    ⨆ coordinate ≤ count, MeasurableSpace.comap (history coordinate) inferInstance
  apply le_antisymm
  · apply iSup_le
    intro coordinate
    exact le_iSup_of_le coordinate.val (le_iSup_of_le (Nat.le_of_lt_succ coordinate.isLt) le_rfl)
  · apply iSup₂_le
    intro coordinate before
    exact le_iSup_of_le (⟨coordinate, Nat.lt_succ_of_le before⟩ : Fin (count+1)) le_rfl

theorem countableHistory_comap_eq_sup_natural_completion
    (history : ℕ → Outcome → Space) (historyStrong : ∀ index, StronglyMeasurable (history index)) :
    MeasurableSpace.comap (fun outcome coordinate => history coordinate outcome) inferInstance =
      ⨆ count, Filtration.natural history historyStrong count := by
  rw [MeasurableSpace.comap_process_pi]
  apply le_antisymm
  · apply iSup_le
    intro coordinate
    exact le_iSup_of_le coordinate (le_iSup_of_le coordinate (le_iSup_of_le le_rfl le_rfl))
  · apply iSup_le
    intro count
    apply iSup₂_le
    intro coordinate _
    exact le_iSup (fun index : ℕ => MeasurableSpace.comap (history index) (inferInstance : MeasurableSpace Space)) coordinate

/-- Lévy's upward theorem promotes genuine finite-past conditional
expectations to the complete countable past. No full-past Markov property
is assumed. -/
theorem conditional_expectation_of_all_finite_histories_completion
    (law : Measure Outcome) [IsFiniteMeasure law]
    (history : ℕ → Outcome → Space) (historyStrong : ∀ index, StronglyMeasurable (history index))
    (future expectation : Outcome → ℝ)
    (finite : ∀ count,
      law[future | MeasurableSpace.comap
        (fun outcome => fun coordinate : Fin (count+1) => history coordinate.val outcome) inferInstance] =ᵐ[law] expectation) :
    law[future | MeasurableSpace.comap (fun outcome coordinate => history coordinate outcome) inferInstance] =ᵐ[law] expectation := by
  have stable (count : ℕ) : law[future | Filtration.natural history historyStrong count] =ᵐ[law] expectation := by
    simpa only [finiteHistory_comap_eq_natural_completion history historyStrong count] using finite count
  have convergence := tendsto_ae_condExp (μ := law) (ℱ := Filtration.natural history historyStrong) future
  rw [countableHistory_comap_eq_sup_natural_completion history historyStrong]
  filter_upwards [convergence, ae_all_iff.mpr stable] with outcome converge same
  have constantLimit : Tendsto (fun count => (law[future | Filtration.natural history historyStrong count]) outcome)
      atTop (𝓝 (expectation outcome)) := tendsto_const_nhds.congr (fun count => (same count).symm)
  exact tendsto_nhds_unique converge constantLimit

end
end IGSIII34.Diffusion
