import IGSIII.Geometry.FiniteSkeleton
import Mathlib.Topology.MetricSpace.GromovHausdorff

/-!
# Gromov--Hausdorff control of finite chemical skeletons

A surjective matching with small distortion controls the actual GH distance.
On a fixed finite vertex set, convergence of every pair distance suffices.
This is only the finite-skeleton step; no full-cluster convergence is assumed.
-/

set_option autoImplicit false

namespace IGSIII.Geometry

open Filter GromovHausdorff
open scoped Topology

variable {Source Target : Type*}
    [MetricSpace Source] [CompactSpace Source] [Nonempty Source]
    [MetricSpace Target] [CompactSpace Target] [Nonempty Target]

theorem ghDist_le_of_surjective_distortion (matching : Source → Target)
    (surjective : Function.Surjective matching) (error : ℝ)
    (distortion : ∀ left right,
      |dist left right - dist (matching left) (matching right)| ≤ error) :
    ghDist Source Target ≤ error / 2 := by
  have bound := ghDist_le_of_approx_subsets
    (s := Set.univ) (fun point => matching point.val)
    (ε₁ := 0) (ε₂ := error) (ε₃ := 0)
    (fun point => ⟨point, Set.mem_univ point, by simp⟩)
    (fun point => by
      obtain ⟨preimage, equality⟩ := surjective point
      exact ⟨⟨preimage, Set.mem_univ preimage⟩, by simp [equality]⟩)
    (fun left right => distortion left.val right.val)
  simpa using bound

variable (Approximant : ℕ → Type*) [∀ depth, MetricSpace (Approximant depth)]
    [∀ depth, CompactSpace (Approximant depth)] [∀ depth, Nonempty (Approximant depth)]

theorem ghDist_tendsto_zero_of_finite_matching [Finite Target]
    (matching : ∀ depth, Approximant depth ≃ Target)
    (converges : ∀ left right : Target,
      Tendsto (fun depth => dist ((matching depth).symm left) ((matching depth).symm right))
        atTop (𝓝 (dist left right))) :
    Tendsto (fun depth => ghDist (Approximant depth) Target) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro epsilon positive
  have eventuallyClose : ∀ᶠ depth in atTop, ∀ left right : Target,
      |dist ((matching depth).symm left) ((matching depth).symm right) -
        dist left right| < epsilon := by
    apply Filter.eventually_all.mpr
    intro left
    apply Filter.eventually_all.mpr
    intro right
    exact (Metric.tendsto_nhds.mp (converges left right) epsilon positive).mono
      (fun _ bound => by simpa [Real.dist_eq] using bound)
  obtain ⟨start, small⟩ := eventually_atTop.mp eventuallyClose
  refine ⟨start, fun depth beyond => ?_⟩
  have bound : ghDist (Approximant depth) Target ≤ epsilon / 2 :=
    ghDist_le_of_surjective_distortion (matching depth) (matching depth).surjective epsilon
      (fun left right => by
        simpa using (small depth beyond ((matching depth) left) ((matching depth) right)).le)
  have nonnegative : 0 ≤ ghDist (Approximant depth) Target := by
    exact dist_nonneg
  rw [Real.dist_eq, sub_zero, abs_of_nonneg nonnegative]
  linarith

end IGSIII.Geometry
