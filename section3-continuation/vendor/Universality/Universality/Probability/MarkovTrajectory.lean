import Mathlib.Probability.Kernel.IonescuTulcea.Traj

/-! Infinite trajectories for time-dependent state spaces, with their one-time laws. -/

namespace Universality
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]

def pastKernel (transition : ∀ n, Kernel (X n) (X (n + 1))) (n : ℕ) :
    Kernel (Π i : Finset.Iic n, X i) (X (n + 1)) :=
  (transition n).comap (fun history => history ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
    (measurable_pi_apply _)

instance (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)] (n : ℕ) :
    IsMarkovKernel (pastKernel transition n) := by
  unfold pastKernel
  infer_instance

def markovTrajectory (initial : Measure (X 0))
    (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)] : Measure (Π n, X n) :=
  Kernel.trajMeasure initial (pastKernel transition)

instance (initial : Measure (X 0)) [IsProbabilityMeasure initial]
    (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)] :
    IsProbabilityMeasure (markovTrajectory initial transition) := by
  unfold markovTrajectory
  infer_instance

theorem markovTrajectory_zero (initial : Measure (X 0))
    (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)] :
    (markovTrajectory initial transition).map (fun path => path 0) = initial := by
  calc
    _ = ((markovTrajectory initial transition).map (frestrictLe 0)).map
        (fun history => history ⟨0, Finset.mem_Iic.mpr le_rfl⟩) :=
      (Measure.map_map (measurable_pi_apply ⟨0, Finset.mem_Iic.mpr le_rfl⟩)
        (measurable_frestrictLe 0)).symm
    _ = initial := by
      rw [markovTrajectory, Kernel.trajMeasure, Measure.map_comp _ _ (by fun_prop),
        Kernel.traj_map_frestrictLe, Kernel.partialTraj_self, Measure.id_comp]
      rw [Measure.map_map (measurable_pi_apply _) (by fun_prop)]
      change initial.map id = initial
      exact Measure.map_id

theorem markovTrajectory_succ (initial : Measure (X 0)) [IsProbabilityMeasure initial]
    (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)] (n : ℕ) :
    (markovTrajectory initial transition).map (fun path => path (n + 1)) =
      transition n ∘ₘ (markovTrajectory initial transition).map (fun path => path n) := by
  have hjoint := Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure
    (μ₀ := initial) (κ := pastKernel transition) (a := n)
  have hsnd := congrArg Measure.snd hjoint
  rw [Measure.snd_compProd, Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)] at hsnd
  change pastKernel transition n ∘ₘ
      (markovTrajectory initial transition).map (frestrictLe n) =
    (markovTrajectory initial transition).map (fun path => path (n + 1)) at hsnd
  rw [← hsnd, pastKernel, ← Kernel.comp_deterministic_eq_comap, ← Measure.comp_assoc,
    Measure.deterministic_comp_eq_map, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

theorem markovTrajectory_marginal (law : ∀ n, Measure (X n))
    [IsProbabilityMeasure (law 0)]
    (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)]
    (hstep : ∀ n, transition n ∘ₘ law n = law (n + 1)) (n : ℕ) :
    (markovTrajectory (law 0) transition).map (fun path => path n) = law n := by
  induction n with
  | zero => exact markovTrajectory_zero _ _
  | succ n ih => rw [markovTrajectory_succ, ih, hstep]

theorem markovTrajectory_step_ae (initial : Measure (X 0)) [IsProbabilityMeasure initial]
    (transition : ∀ n, Kernel (X n) (X (n + 1)))
    [∀ n, IsMarkovKernel (transition n)] (n : ℕ) (property : X n → X (n + 1) → Prop)
    (hmeas : MeasurableSet {pair : X n × X (n + 1) | property pair.1 pair.2})
    (hstep : ∀ x, ∀ᵐ y ∂transition n x, property x y) :
    ∀ᵐ path ∂markovTrajectory initial transition, property (path n) (path (n + 1)) := by
  have h : ∀ᵐ pair ∂((markovTrajectory initial transition).map (frestrictLe n) ⊗ₘ
      pastKernel transition n),
      property (pair.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩) pair.2 := by
    apply Measure.ae_compProd_of_ae_ae
    · exact (by fun_prop : Measurable (fun pair : (Π i : Finset.Iic n, X i) × X (n + 1) =>
        (pair.1 ⟨n, Finset.mem_Iic.mpr le_rfl⟩, pair.2))) hmeas
    · apply Filter.Eventually.of_forall
      intro history
      simpa only [pastKernel, Kernel.comap_apply] using
        hstep (history ⟨n, Finset.mem_Iic.mpr le_rfl⟩)
  change ∀ᵐ pair ∂((Kernel.trajMeasure initial (pastKernel transition)).map (frestrictLe n) ⊗ₘ
      pastKernel transition n), _ at h
  rw [Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure] at h
  exact ae_of_ae_map (by fun_prop) h

end
end Universality
