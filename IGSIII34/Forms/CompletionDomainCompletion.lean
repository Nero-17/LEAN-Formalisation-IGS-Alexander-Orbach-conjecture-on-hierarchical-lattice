import IGSIII34.Forms.CompletionExtension
import Mathlib.Topology.ContinuousMap.StoneWeierstrass

/-! The domain on the actual metric completion is defined by restriction to
the dense skeleton. It contains exactly the unique extensions of finite-energy
skeleton functions. No unconstrained functions outside the skeleton enter. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

variable {Carrier : Type*} [MetricSpace Carrier]
variable {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
variable (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
variable (conductance : ∀ depth, Edge depth → ℝ)
variable (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
variable (resistanceBound : ∀ potential ∈ energyDomain endpoint conductance nonnegative,
  ∀ first second, (potential first - potential second) ^ 2 ≤
    dist first second * limitingEnergy endpoint conductance potential)

def completionEnergyDomain : Submodule ℝ C(UniformSpace.Completion Carrier, ℝ) where
  carrier := {potential | (fun point : Carrier => potential point) ∈
    energyDomain endpoint conductance nonnegative}
  zero_mem' := (energyDomain endpoint conductance nonnegative).zero_mem
  add_mem' {first second} firstFinite secondFinite :=
    (energyDomain endpoint conductance nonnegative).add_mem firstFinite secondFinite
  smul_mem' scalar {potential} finite :=
    (energyDomain endpoint conductance nonnegative).smul_mem scalar finite

theorem completionEnergyDomain_eq_extension_range :
    (completionEnergyDomain endpoint conductance nonnegative : Set C(UniformSpace.Completion Carrier, ℝ)) =
      Set.range (completionExtensionLinear endpoint conductance nonnegative resistanceBound) := by
  ext potential
  constructor
  · intro finite
    refine ⟨⟨fun point => potential point, finite⟩, ?_⟩
    apply DFunLike.coe_injective
    apply (UniformSpace.Completion.denseRange_coe (α := Carrier)).equalizer
      (completionExtension endpoint conductance nonnegative ⟨_, finite⟩).continuous potential.continuous
    funext point
    exact completionExtension_coe endpoint conductance nonnegative resistanceBound ⟨_, finite⟩ point
  · rintro ⟨potential, rfl⟩
    change (fun point : Carrier => completionExtension endpoint conductance nonnegative potential point) ∈
      energyDomain endpoint conductance nonnegative
    simpa only [completionExtension_coe endpoint conductance nonnegative resistanceBound] using potential.property

theorem completionEnergyDomain_constant (constant : ℝ) :
    ContinuousMap.const (UniformSpace.Completion Carrier) constant ∈
      completionEnergyDomain endpoint conductance nonnegative := by
  refine ⟨0, ?_⟩
  rintro value ⟨depth, rfl⟩
  exact (finiteEnergy_constant (endpoint depth) (conductance depth) constant).le

theorem completionEnergyDomain_normal_contraction
    (contraction : ℝ → ℝ) (continuous : Continuous contraction)
    (contracts : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    {potential : C(UniformSpace.Completion Carrier, ℝ)}
    (finite : potential ∈ completionEnergyDomain endpoint conductance nonnegative) :
    (⟨fun point => contraction (potential point), continuous.comp potential.continuous⟩ :
      C(UniformSpace.Completion Carrier, ℝ)) ∈ completionEnergyDomain endpoint conductance nonnegative :=
  energyDomain_normal_contraction endpoint conductance nonnegative contraction contracts finite

theorem completionEnergyDomain_abs
    {potential : C(UniformSpace.Completion Carrier, ℝ)}
    (finite : potential ∈ completionEnergyDomain endpoint conductance nonnegative) :
    (⟨fun point => |potential point|, potential.continuous.abs⟩ :
      C(UniformSpace.Completion Carrier, ℝ)) ∈ completionEnergyDomain endpoint conductance nonnegative :=
  completionEnergyDomain_normal_contraction endpoint conductance nonnegative abs continuous_abs
    (fun first second => abs_abs_sub_abs_le_abs_sub first second) finite

theorem completionEnergyDomain_sup
    {first second : C(UniformSpace.Completion Carrier, ℝ)}
    (firstFinite : first ∈ completionEnergyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ completionEnergyDomain endpoint conductance nonnegative) :
    first ⊔ second ∈ completionEnergyDomain endpoint conductance nonnegative := by
  have differenceFinite := (completionEnergyDomain endpoint conductance nonnegative).sub_mem firstFinite secondFinite
  have absoluteFinite := completionEnergyDomain_abs endpoint conductance nonnegative differenceFinite
  have sumFinite := (completionEnergyDomain endpoint conductance nonnegative).add_mem
    ((completionEnergyDomain endpoint conductance nonnegative).add_mem firstFinite secondFinite) absoluteFinite
  have scaled := (completionEnergyDomain endpoint conductance nonnegative).smul_mem (1 / 2 : ℝ) sumFinite
  convert scaled using 1
  apply DFunLike.coe_injective
  funext point
  change max (first point) (second point) = (1 / 2 : ℝ) * (first point + second point + |first point - second point|)
  rw [max_def]
  split_ifs with ordered
  · rw [abs_of_nonpos (sub_nonpos.mpr ordered)]
    ring
  · rw [abs_of_nonneg (sub_nonneg.mpr (le_of_not_ge ordered))]
    ring

theorem completionEnergyDomain_inf
    {first second : C(UniformSpace.Completion Carrier, ℝ)}
    (firstFinite : first ∈ completionEnergyDomain endpoint conductance nonnegative)
    (secondFinite : second ∈ completionEnergyDomain endpoint conductance nonnegative) :
    first ⊓ second ∈ completionEnergyDomain endpoint conductance nonnegative := by
  have supremumFinite := completionEnergyDomain_sup endpoint conductance nonnegative
    ((completionEnergyDomain endpoint conductance nonnegative).neg_mem firstFinite)
    ((completionEnergyDomain endpoint conductance nonnegative).neg_mem secondFinite)
  have negated := (completionEnergyDomain endpoint conductance nonnegative).neg_mem supremumFinite
  convert negated using 1
  apply DFunLike.coe_injective
  funext point
  change min (first point) (second point) = -max (-first point) (-second point)
  by_cases ordered : first point ≤ second point
  · rw [min_eq_left ordered, max_eq_left (neg_le_neg ordered), neg_neg]
  · rw [min_eq_right (le_of_not_ge ordered), max_eq_right (neg_le_neg (le_of_not_ge ordered)), neg_neg]

end
end IGSIII34.Forms
