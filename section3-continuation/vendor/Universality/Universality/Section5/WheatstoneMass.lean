import Universality.Section5.HeterogeneousMass
import Universality.Section5.WheatstoneResponse
import Universality.Section5.WheatstoneMassKernels

namespace Universality.Section5
noncomputable section
open FiniteNetwork Matrix

/-- The exact three-state mass recursion of the actual glued Wheatstone rule. -/
theorem wheatstoneRule_massMatrix (a b c : Rule)
    (a_fixed : a.network.reliability (1 / 2) = 1 / 2)
    (b_fixed : b.network.reliability (1 / 2) = 1 / 2)
    (c_fixed : c.network.reliability (1 / 2) = 1 / 2)
    (symmetry : ∀ edge : Fin 5, (![a,b,b,a,c] edge).network.NetworkSymmetry)
    (source_target : ∀ edge, (symmetry edge).vertex (![a,b,b,a,c] edge).network.source =
      (![a,b,b,a,c] edge).network.target)
    (target_source : ∀ edge, (symmetry edge).vertex (![a,b,b,a,c] edge).network.target =
      (![a,b,b,a,c] edge).network.source) :
    (wheatstoneRule a b c).network.massMatrix (1 / 2) =
      K3real * a.network.massMatrix (1 / 2) + K3real * b.network.massMatrix (1 / 2) +
        J3real * c.network.massMatrix (1 / 2) := by
  have common : ∀ edge : Fin 5, (![a,b,b,a,c] edge).network.reliability (1 / 2) = 1 / 2 := by
    intro edge
    fin_cases edge <;> first | exact a_fixed | exact b_fixed | exact c_fixed
  have matrices (edge : Fin 5) :
      (![a,b,b,a,c] edge).network.massMatrix (1 / 2) =
        ![a.network.massMatrix (1 / 2), b.network.massMatrix (1 / 2),
          b.network.massMatrix (1 / 2), a.network.massMatrix (1 / 2),
          c.network.massMatrix (1 / 2)] edge := by
    fin_cases edge <;> rfl
  ext σ τ
  change (wheatstoneNetwork.heterogeneousSubstitute
    (fun edge : Fin 5 => (![a,b,b,a,c] edge).network)).massMatrix (1 / 2) σ τ = _
  rw [heterogeneousSubstitute_massMatrix_common wheatstoneNetwork _ (1 / 2) (1 / 2)
    common (by norm_num) (by norm_num) symmetry source_target target_source]
  simp_rw [matrices]
  exact wheatstone_mass_kernel_aggregation _ _ _ σ τ

end
end Universality.Section5
