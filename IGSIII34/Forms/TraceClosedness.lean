import IGSIII34.ResistanceLimit.LimitEnergy

/-! Lower semicontinuity of the supremum trace energy under pointwise
convergence. This supplies the closedness step without assuming closedness.
-/
set_option autoImplicit false
namespace IGSIII34.Forms
noncomputable section
open IGSIII34.ResistanceLimit Filter
open scoped Topology

theorem finiteEnergy_tendsto_of_pointwise
    {Carrier Edge : Type*} [Fintype Edge]
    (endpoint : Edge → Carrier × Carrier) (conductance : Edge → ℝ)
    (sequence : ℕ → Carrier → ℝ) (limit : Carrier → ℝ)
    (convergence : ∀ point, Tendsto (fun index => sequence index point) atTop (𝓝 (limit point))) :
    Tendsto (fun index => finiteEnergy endpoint conductance (sequence index)) atTop
      (𝓝 (finiteEnergy endpoint conductance limit)) := by
  apply tendsto_finsetSum
  intro edge _
  exact (((convergence (endpoint edge).1).sub (convergence (endpoint edge).2)).pow 2).const_mul _

theorem finite_energy_limit_of_uniform_bound
    {Carrier : Type*} {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
    (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
    (conductance : ∀ depth, Edge depth → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
    (sequence : ℕ → Carrier → ℝ) (limit : Carrier → ℝ) (bound : ℝ)
    (convergence : ∀ point, Tendsto (fun index => sequence index point) atTop (𝓝 (limit point)))
    (bounds : ∀ᶠ index in atTop, ∀ depth, traceEnergy endpoint conductance depth (sequence index) ≤ bound) :
    limit ∈ energyDomain endpoint conductance nonnegative ∧
      limitingEnergy endpoint conductance limit ≤ bound := by
  have traceBounds : ∀ depth, traceEnergy endpoint conductance depth limit ≤ bound := by
    intro depth
    exact le_of_tendsto (finiteEnergy_tendsto_of_pointwise (endpoint depth) (conductance depth)
      sequence limit convergence) (bounds.mono (fun _ bounded => bounded depth))
  have finite : limit ∈ energyDomain endpoint conductance nonnegative := by
    refine ⟨bound, ?_⟩
    rintro value ⟨depth, rfl⟩
    exact traceBounds depth
  exact ⟨finite, ciSup_le traceBounds⟩

theorem limiting_energy_limit_of_uniform_bound
    {Carrier : Type*} {Edge : ℕ → Type*} [∀ depth, Fintype (Edge depth)]
    (endpoint : ∀ depth, Edge depth → Carrier × Carrier)
    (conductance : ∀ depth, Edge depth → ℝ)
    (nonnegative : ∀ depth edge, 0 ≤ conductance depth edge)
    (sequence : ℕ → Carrier → ℝ) (limit : Carrier → ℝ) (bound : ℝ)
    (finite : ∀ index, sequence index ∈ energyDomain endpoint conductance nonnegative)
    (convergence : ∀ point, Tendsto (fun index => sequence index point) atTop (𝓝 (limit point)))
    (bounds : ∀ᶠ index in atTop, limitingEnergy endpoint conductance (sequence index) ≤ bound) :
    limit ∈ energyDomain endpoint conductance nonnegative ∧
      limitingEnergy endpoint conductance limit ≤ bound := by
  apply finite_energy_limit_of_uniform_bound endpoint conductance nonnegative sequence limit bound convergence
  filter_upwards [bounds] with index bound depth
  exact (traceEnergy_le_limitingEnergy endpoint conductance nonnegative (finite index) depth).trans bound

end
end IGSIII34.Forms
