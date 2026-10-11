import Universality.Probability.IndependentSumLaw
import Universality.Percolation.VertexMassSmoothing

namespace Universality.FiniteNetwork
noncomputable section
open MeasureTheory
open scoped ENNReal

def childMassLaw {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) (state : LiveState) (coarse : Configuration edges)
    (edge : Fin edges) : Measure ℝ :=
  match R.childState state coarse edge with
  | none => Measure.dirac 0
  | some child => law child

instance childMassLaw_probability {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (state : LiveState) (coarse : Configuration edges) (edge : Fin edges) :
    IsProbabilityMeasure (R.childMassLaw law state coarse edge) := by
  unfold childMassLaw
  cases R.childState state coarse edge <;> infer_instance

def offspringMassLaw {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) (radius : ℝ) (state : LiveState) (coarse : Configuration edges) : Measure ℝ :=
  (independentSumLaw (R.childMassLaw law state coarse)).map (fun x => radius⁻¹ * x)

instance offspringMassLaw_probability {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (radius : ℝ) (state : LiveState) (coarse : Configuration edges) :
    IsProbabilityMeasure (R.offspringMassLaw law radius state coarse) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

theorem offspringMassLaw_charFun {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (radius : ℝ) (state : LiveState) (coarse : Configuration edges) (t : ℝ) :
    charFun (R.offspringMassLaw law radius state coarse) t =
      ∏ edge, match R.childState state coarse edge with
        | none => 1
        | some child => charFun (law child) (t / radius) := by
  rw [offspringMassLaw, charFun_map_mul, independentSumLaw_charFun]
  apply Finset.prod_congr rfl
  intro edge _
  unfold childMassLaw
  cases R.childState state coarse edge with
  | none => simp [charFun_dirac]
  | some child => congr 1; ring

theorem mass_smoothing_law_of_characteristic {vertices edges : ℕ} (R : FiniteNetwork vertices edges)
    (law : LiveState → Measure ℝ) [∀ state, IsProbabilityMeasure (law state)]
    (p radius : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < R.reliability p) (hless : R.reliability p < 1)
    (hsmoothing : ∀ state t, charFun (law state) t =
      ∑ coarse, (R.conditionalCellWeight p (state == .connected) coarse : ℂ) *
        ∏ edge, match R.childState state coarse edge with
          | none => 1
          | some child => charFun (law child) (t / radius)) (state : LiveState) :
    law state = finiteMixtureLaw (R.conditionalCellWeight p (state == .connected))
      (R.offspringMassLaw law radius state) := by
  letI := finiteMixtureLaw_probability (R.conditionalCellWeight p (state == .connected))
    (R.offspringMassLaw law radius state)
    (fun coarse => R.conditionalCellWeight_nonneg hp hp' _ coarse)
    (R.sum_conditionalCellWeight p hpositive hless _)
  apply Measure.ext_of_charFun
  funext t
  rw [finiteMixtureLaw_charFun _ _ (fun coarse => R.conditionalCellWeight_nonneg hp hp' _ coarse), hsmoothing]
  apply Finset.sum_congr rfl
  intro coarse _
  rw [R.offspringMassLaw_charFun]

end
end Universality.FiniteNetwork

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix MeasureTheory Filter
open scoped Topology ENNReal

/-- Fourier uniqueness upgrades the actual limit recursion to equality with
the mixture of independent-child sum laws, for any same-limit family. -/
theorem Classical.mass_limit_distribution_smoothing {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (limit : LiveState → (Π n, rule.ConfigurationHistory n) → ℝ)
    (hmem : ∀ state, MemLp (limit state) 2
      (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)))
    (huniform : ∀ state bound, TendstoUniformlyOn
      (fun n t => (rule.generation n).network.conditionalVertexCharacteristic p state
        (t / ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) ^ n))
      (charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state)))
      atTop {t : ℝ | |t| ≤ bound}) (state : LiveState) :
    (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (state == .connected)).map (limit state) =
      finiteMixtureLaw (rule.network.conditionalCellWeight p (state == .connected))
        (rule.network.offspringMassLaw
          (fun child => (ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child))
          ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal) state) := by
  letI (child : LiveState) := Measure.isProbabilityMeasure_map (hmem child).aestronglyMeasurable.aemeasurable
  obtain ⟨other, _, _, _, hotherUniform, hotherSmoothing⟩ := h.internal_vertex_mass_smoothing p hp hp' hfixed
  have heq (child : LiveState) (t : ℝ) :
      charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (limit child)) t =
      charFun ((ConfigurationHistory.infiniteLaw rule p hp hp' hfixed (child == .connected)).map (other child)) t :=
    tendsto_nhds_unique
      ((huniform child |t|).tendsto_at (x := t) (show |t| ≤ |t| from le_rfl))
      ((hotherUniform child |t|).tendsto_at (x := t) (show |t| ≤ |t| from le_rfl))
  apply rule.network.mass_smoothing_law_of_characteristic _ p _ hp.le hp'.le
    (by rwa [hfixed]) (by rwa [hfixed]) _ state
  intro parent t
  rw [heq, hotherSmoothing]
  apply Finset.sum_congr rfl
  intro coarse _
  congr 1
  apply Finset.prod_congr rfl
  intro edge _
  cases rule.network.childState parent coarse edge with
  | none => rfl
  | some child => exact (heq child _).symm

end
end Universality.Rule
