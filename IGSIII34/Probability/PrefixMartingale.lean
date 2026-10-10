import Mathlib.Probability.Martingale.Convergence
import Mathlib.MeasureTheory.Constructions.Pi

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Probability
noncomputable section
open MeasureTheory Filter
open scoped _root_.Topology
variable {Index : Type*} {State : Index → Type*} [∀ index, MeasurableSpace (State index)]

def coordinatePrefixFiltration (rank : Index → ℕ) : Filtration ℕ (inferInstance : MeasurableSpace ((index : Index) → State index)) where
  seq depth := ⨆ index, ⨆ (_ : rank index < depth),
    (inferInstance : MeasurableSpace (State index)).comap (fun sample : (index : Index) → State index => sample index)
  mono' := by
    intro first second comparison
    apply iSup_le
    intro index
    apply iSup_le
    intro within
    exact le_iSup_of_le index (le_iSup_of_le (within.trans_le comparison) le_rfl)
  le' depth := by
    apply iSup_le
    intro index
    apply iSup_le
    intro _
    exact measurable_pi_apply index |>.comap_le

theorem coordinatePrefixFiltration_generates (rank : Index → ℕ) :
    (⨆ depth : ℕ, coordinatePrefixFiltration rank depth) =
      (inferInstance : MeasurableSpace ((index : Index) → State index)) := by
  apply le_antisymm
  · exact iSup_le (fun depth => (coordinatePrefixFiltration rank).le depth)
  · change (⨆ index, (inferInstance : MeasurableSpace (State index)).comap
        (fun sample : (index : Index) → State index => sample index)) ≤ _
    apply iSup_le
    intro index
    apply le_iSup_of_le (rank index+1)
    change _ ≤ ⨆ coordinate, ⨆ (_ : rank coordinate < rank index+1), _
    exact le_iSup_of_le index (le_iSup_of_le (Nat.lt_succ_self (rank index)) le_rfl)

theorem coordinatePrefixFiltration_eq_comap (rank : Index → ℕ) (depth : ℕ) :
    coordinatePrefixFiltration (State := State) rank depth =
      (inferInstance : MeasurableSpace ((index : {index : Index // rank index < depth}) → State index.val)).comap
        (fun sample : (index : Index) → State index => fun index : {index : Index // rank index < depth} => sample index.val) := by
  change (⨆ index, ⨆ (_ : rank index < depth), (inferInstance : MeasurableSpace (State index)).comap
    (fun sample : (index : Index) → State index => sample index)) = _
  simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]
  apply le_antisymm
  · apply iSup_le
    intro index
    apply iSup_le
    intro within
    exact le_iSup_of_le ⟨index, within⟩ le_rfl
  · apply iSup_le
    intro index
    exact le_iSup_of_le index.val (le_iSup_of_le index.property le_rfl)

theorem coordinatePrefixFiltration_condExp_tendsto (rank : Index → ℕ)
    (measure : Measure ((index : Index) → State index)) [IsFiniteMeasure measure]
    (value : ((index : Index) → State index) → ℝ) (measurable : StronglyMeasurable value)
    (integrable : Integrable value measure) :
    ∀ᵐ sample ∂measure,
      Tendsto (fun depth => measure[value | coordinatePrefixFiltration rank depth] sample)
        atTop (𝓝 (value sample)) := by
  apply integrable.tendsto_ae_condExp
  rw [coordinatePrefixFiltration_generates rank]
  exact measurable

end
end IGSIII34.Probability
