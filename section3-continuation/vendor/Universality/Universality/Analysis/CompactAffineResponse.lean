import Mathlib.Topology.Order.Compact
import Universality.Analysis.DiscountedIteration

namespace Universality
noncomputable section
open Set

/-- A continuous solution of a positive affine renormalization with coefficient
below one is nonnegative. Compactness removes any need to estimate infinite
products along the orbit. -/
theorem nonneg_of_compact_affine_renormalization {space : Type*} [TopologicalSpace space]
    (domain : Set space) (hcompact : IsCompact domain) (hnonempty : domain.Nonempty)
    (iteration : space → space) (response coefficient forcing : space → ℝ)
    (hmaps : MapsTo iteration domain domain) (hresponse : ContinuousOn response domain)
    (hcoefficient : ∀ point ∈ domain, 0 ≤ coefficient point ∧ coefficient point < 1)
    (hforcing : ∀ point ∈ domain, 0 ≤ forcing point)
    (hequation : ∀ point ∈ domain,
      response point = coefficient point * response (iteration point) + forcing point) :
    ∀ point ∈ domain, 0 ≤ response point := by
  obtain ⟨minimum, hminimumMem, hminimum⟩ := hcompact.exists_isMinOn hnonempty hresponse
  have hminimumNonneg : 0 ≤ response minimum := by
    by_contra hnegative
    have hnegative : response minimum < 0 := lt_of_not_ge hnegative
    have hbound := hminimum (hmaps hminimumMem)
    have hscaled := mul_le_mul_of_nonneg_left hbound (hcoefficient minimum hminimumMem).1
    have heq := hequation minimum hminimumMem
    have hf := hforcing minimum hminimumMem
    have ha := (hcoefficient minimum hminimumMem).2
    nlinarith
  intro point hp
  exact hminimumNonneg.trans (hminimum hp)

end
end Universality
