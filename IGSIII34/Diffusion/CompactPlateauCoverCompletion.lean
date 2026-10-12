import IGSIII34.Diffusion.CountablePathContinuityCompletion
import Mathlib.Topology.ContinuousMap.Compact

set_option autoImplicit false
set_option maxHeartbeats 3000000

namespace IGSIII34.Diffusion
noncomputable section
open Set Metric
open scoped Topology
variable {Space : Type*} [MetricSpace Space] [CompactSpace Space]

def compactPlateauCompletion (center : Space) (radius : ℝ) : C(Space, ℝ) :=
  ⟨fun point => max 0 (min 1 (2 - 8 * dist point center / radius)), by fun_prop⟩

theorem compactPlateau_unit_interval_completion (center : Space) (radius : ℝ) (point : Space) :
    0 ≤ compactPlateauCompletion center radius point ∧
      compactPlateauCompletion center radius point ≤ 1 := by
  change 0 ≤ max 0 (min 1 _) ∧ max 0 (min 1 _) ≤ 1
  exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

theorem compactPlateau_one_completion (center : Space) (radius : ℝ) (radiusPositive : 0 < radius)
    (point : Space) (near : dist point center ≤ radius / 8) :
    compactPlateauCompletion center radius point = 1 := by
  have scaled : 8 * dist point center / radius ≤ 1 := by
    apply (div_le_iff₀ radiusPositive).mpr
    linarith
  simp only [compactPlateauCompletion, ContinuousMap.coe_mk]
  rw [min_eq_left (by linarith), max_eq_right (by norm_num)]

theorem compactPlateau_zero_completion (center : Space) (radius : ℝ) (radiusPositive : 0 < radius)
    (point : Space) (far : radius / 4 ≤ dist point center) :
    compactPlateauCompletion center radius point = 0 := by
  have scaled : 2 ≤ 8 * dist point center / radius := by
    apply (le_div_iff₀ radiusPositive).mpr
    linarith
  change max 0 (min 1 _) = 0
  apply max_eq_left
  exact (min_le_right _ _).trans (by linarith)

/-- Fixed finite plateau functions, selected only from the target spatial
radius. Their number is independent of every later resolvent error. -/
theorem exists_compact_plateau_cover_completion (radius : ℝ) (radiusPositive : 0 < radius) :
    ∃ centers : Set Space, centers.Finite ∧
      ∀ point, ∃ center : centers, compactPlateauCompletion center.val radius point = 1 := by
  obtain ⟨centers, _, finite, cover⟩ := finite_cover_balls_of_compact
    (isCompact_univ (X := Space)) (show 0 < radius / 8 by positivity)
  refine ⟨centers, finite, ?_⟩
  intro point
  have covered := cover (Set.mem_univ point)
  simp only [Set.mem_iUnion] at covered
  obtain ⟨center, member, near⟩ := covered
  refine ⟨⟨center, member⟩, compactPlateau_one_completion center radius radiusPositive point ?_⟩
  exact (by simpa only [Metric.mem_ball, dist_comm] using near : dist point center < radius / 8).le

/-- Uniform approximations to these fixed plateaux are a genuine cover of
all vertices and separate any two vertices at the prescribed distance. -/
theorem compactPlateau_approximation_cover_completion
    {Vertex Label : Type*} (centers : Label → Space) (embedding : Vertex → Space)
    (radius : ℝ) (radiusPositive : 0 < radius) (error : ℝ) (errorNonnegative : 0 ≤ error) (errorBelowHalf : error < 1 / 2)
    (cover : ∀ point, ∃ label, compactPlateauCompletion (centers label) radius point = 1)
    (potential : Label → Vertex → ℝ)
    (approximation : ∀ label vertex,
      |potential label vertex - compactPlateauCompletion (centers label) radius (embedding vertex)| ≤ error) :
    (∀ vertex, ∃ label, 1 - error ≤ potential label vertex) ∧
      (∀ label first last, 1 - error ≤ potential label first → radius ≤ dist (embedding first) (embedding last) →
        potential label last ≤ error) := by
  refine ⟨?_, ?_⟩
  · intro vertex
    obtain ⟨label, plateau⟩ := cover (embedding vertex)
    refine ⟨label, ?_⟩
    have bound := (abs_le.mp (approximation label vertex)).1
    rw [plateau] at bound
    linarith
  · intro label first last initial far
    have inside : dist (embedding first) (centers label) < radius / 4 := by
      by_contra contrary
      have zero := compactPlateau_zero_completion (centers label) radius radiusPositive
        (embedding first) (le_of_not_gt contrary)
      have upper := (abs_le.mp (approximation label first)).2
      rw [zero] at upper
      linarith
    have outside : radius / 4 ≤ dist (embedding last) (centers label) := by
      have triangle := dist_triangle (embedding first) (centers label) (embedding last)
      rw [dist_comm (centers label) (embedding last)] at triangle
      linarith
    have zero := compactPlateau_zero_completion (centers label) radius radiusPositive (embedding last) outside
    have upper := (abs_le.mp (approximation label last)).2
    rw [zero] at upper
    linarith

end
end IGSIII34.Diffusion
