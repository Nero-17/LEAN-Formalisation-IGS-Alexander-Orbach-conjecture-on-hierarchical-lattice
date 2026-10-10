import Mathlib.Probability.Independence.InfinitePi

/-! Grouping disjoint coordinate families of a product probability space. -/

set_option autoImplicit false

namespace IGSIII.Probability

open MeasureTheory ProbabilityTheory

variable {Index Group Value : Type*} {localIndex : Group → Type*}
    [MeasurableSpace Value] (law : Index → Measure Value)
    [∀ index, IsProbabilityMeasure (law index)]
    (coordinate : (group : Group) × localIndex group → Index)

 theorem infinitePi_subfamilies_map (injective : Function.Injective coordinate) :
    (Measure.infinitePi law).map (fun sample group localIndex => sample (coordinate ⟨group, localIndex⟩)) =
      Measure.infinitePi (fun group => Measure.infinitePi (fun localIndex => law (coordinate ⟨group, localIndex⟩))) := by
  have flat := Measure.map_infinitePi_infinitePi_of_inj (P := law) injective
  have curry := Measure.infinitePi_map_piCurry
    (X := fun (_ : Group) (_ : localIndex _) => Value)
    (fun group localIndex => law (coordinate ⟨group, localIndex⟩))
  rw [← curry, ← flat, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

 theorem infinitePi_subfamilies_independent (injective : Function.Injective coordinate) :
    iIndepFun (fun group sample localIndex => sample (coordinate ⟨group, localIndex⟩))
      (Measure.infinitePi law) := by
  apply (iIndepFun_iff_map_fun_eq_infinitePi_map (by fun_prop)).2
  rw [infinitePi_subfamilies_map law coordinate injective]
  congr 1
  funext group
  exact (Measure.map_infinitePi_infinitePi_of_inj (P := law)
    (fun first second equality => eq_of_heq ((Sigma.mk.inj_iff.mp (injective equality)).2))).symm

end IGSIII.Probability


