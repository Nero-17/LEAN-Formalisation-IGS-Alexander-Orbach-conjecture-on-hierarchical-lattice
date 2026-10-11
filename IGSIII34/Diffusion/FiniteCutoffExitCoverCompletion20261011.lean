import IGSIII34.Diffusion.StoppingWindowHitCompletion20261011

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency true

namespace IGSIII34.Diffusion
noncomputable section
open Universality Universality.FiniteNetwork IGSIII.Geometry
open MeasureTheory ProbabilityTheory Filter Preorder
open scoped BigOperators Topology NNReal

variable {Vertex Edge Label Carrier : Type*} [Fintype Vertex] [DecidableEq Vertex]
  [MeasurableSpace Vertex] [MeasurableSingletonClass Vertex] [Fintype Edge]
  [StandardBorelSpace Vertex] [Nonempty Vertex] [Fintype Label] [MetricSpace Carrier]

/-- A finite separating cutoff cover turns the real conditional first-hit
estimate into a metric escape estimate at every bounded stopping time.
All probabilities are those of the original finite neighbour walk. -/
theorem finiteDiscreteWalkLaw_cutoff_cover_exit_completion20261011
    (endpoint : Edge → Vertex × Vertex) (positiveDegree : ∀ vertex, 0 < degree endpoint vertex)
    (initial : Measure Vertex) [IsProbabilityMeasure initial]
    (embedding : Vertex → Carrier) (potentials : Label → Vertex → ℝ)
    (potentialUpper : ∀ label vertex, potentials label vertex ≤ 1)
    (driftBound : ℝ) (driftNonnegative : 0 ≤ driftBound)
    (generatorBound : ∀ label vertex, |rateOneGenerator endpoint (potentials label) vertex| ≤ driftBound)
    (radius error threshold : ℝ) (errorNonnegative : 0 ≤ error) (thresholdBelowOne : threshold < 1)
    (cover : ∀ vertex, ∃ label, 1 - error ≤ potentials label vertex)
    (separating : ∀ label first last, 1 - error ≤ potentials label first →
      radius ≤ dist (embedding first) (embedding last) → potentials label last ≤ threshold)
    (first : (ℕ → Vertex) → WithTop ℕ) (firstStopping : IsStoppingTime Filtration.piLE first)
    (horizon window : ℕ) (bounded : ∀ path, first path ≤ horizon)
    (event : Set (ℕ → Vertex)) (known : MeasurableSet[firstStopping.measurableSpace] event) :
    (1 - threshold) * (finiteDiscreteWalkLaw endpoint positiveDegree initial).real
      (event ∩ {path | ∃ index, (first path).untopA ≤ index ∧ index ≤ (first path).untopA + window ∧
        radius ≤ dist (embedding (path (first path).untopA)) (embedding (path index))}) ≤
      Fintype.card Label * (error + window * driftBound) *
        (finiteDiscreteWalkLaw endpoint positiveDegree initial).real event := by
  let law := finiteDiscreteWalkLaw endpoint positiveDegree initial
  let startSet (label : Label) := {path : ℕ → Vertex | 1 - error ≤ potentials label (path (first path).untopA)}
  let exitSet (label : Label) := {path : ℕ → Vertex | ∃ index, (first path).untopA ≤ index ∧
    index ≤ (first path).untopA + window ∧ potentials label (path index) ≤ threshold}
  have startKnown (label : Label) : MeasurableSet[firstStopping.measurableSpace] (startSet label) := by
    have adapted : StronglyAdapted Filtration.piLE (fun (index : ℕ) (path : ℕ → Vertex) => potentials label (path index)) :=
      fun index => finitePathPotential_stronglyMeasurable_past_completion20261011 (potentials label) index index le_rfl
    have stopped := measurable_stoppedValue adapted.isStronglyProgressive_of_discrete firstStopping
    exact measurableSet_le measurable_const stopped
  have individual (label : Label) : (1 - threshold) * law.real ((event ∩ startSet label) ∩ exitSet label) ≤
      (error + window * driftBound) * law.real event := by
    have stopped := finiteDiscreteWalkLaw_first_exit_window_completion20261011 endpoint positiveDegree initial
      (potentials label) (potentialUpper label) driftBound driftNonnegative (generatorBound label)
      first firstStopping horizon window bounded (event ∩ startSet label) (known.inter (startKnown label))
      error threshold (fun _path member => member.2)
    change (1 - threshold) * law.real ((event ∩ startSet label) ∩ exitSet label) ≤
      (error + window * driftBound) * law.real (event ∩ startSet label) at stopped
    exact stopped.trans (mul_le_mul_of_nonneg_left
      (measureReal_mono (μ := law) Set.inter_subset_left)
      (add_nonneg errorNonnegative (mul_nonneg (Nat.cast_nonneg _) driftNonnegative)))
  have inclusion :
      (event ∩ {path | ∃ index, (first path).untopA ≤ index ∧ index ≤ (first path).untopA + window ∧
        radius ≤ dist (embedding (path (first path).untopA)) (embedding (path index))}) ⊆
      ⋃ label : Label, ((event ∩ startSet label) ∩ exitSet label) := by
    rintro path ⟨member, index, after, before, far⟩
    obtain ⟨label, covered⟩ := cover (path (first path).untopA)
    exact Set.mem_iUnion.mpr ⟨label, ⟨⟨member, covered⟩,
      ⟨index, after, before, separating label _ _ covered far⟩⟩⟩
  have probabilityBound := (measureReal_mono (μ := law) inclusion).trans
    (measureReal_iUnion_fintype_le (μ := law) fun label => ((event ∩ startSet label) ∩ exitSet label))
  calc
    _ ≤ (1 - threshold) * ∑ label, law.real ((event ∩ startSet label) ∩ exitSet label) :=
      mul_le_mul_of_nonneg_left probabilityBound (by linarith)
    _ = ∑ label, (1 - threshold) * law.real ((event ∩ startSet label) ∩ exitSet label) := Finset.mul_sum _ _ _
    _ ≤ ∑ _label : Label, (error + window * driftBound) * law.real event :=
      Finset.sum_le_sum fun label _ => individual label
    _ = _ := by simp; ring

end
end IGSIII34.Diffusion
