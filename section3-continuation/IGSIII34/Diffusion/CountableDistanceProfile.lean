import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.UniformSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metric
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace IGSIII34.Diffusion
noncomputable section
open Filter Set UniformSpace
open scoped Topology Uniformity

/-- A fixed compact spatial carrier which retains every distance-to-birth
coordinate, without selecting finitely many observation times. -/
def CountableDistanceProfile (Labels : Type*) := Labels → Set.Icc (0 : ℝ) 1

instance {Labels : Type*} : UniformSpace (CountableDistanceProfile Labels) :=
  inferInstanceAs (UniformSpace (Labels → Set.Icc (0 : ℝ) 1))

instance {Labels : Type*} [Countable Labels] : MetricSpace (CountableDistanceProfile Labels) :=
  UniformSpace.metricSpace (Labels → Set.Icc (0 : ℝ) 1)

instance {Labels : Type*} : CompactSpace (CountableDistanceProfile Labels) :=
  inferInstanceAs (CompactSpace (Labels → Set.Icc (0 : ℝ) 1))

instance {Labels : Type*} [Countable Labels] : SecondCountableTopology (CountableDistanceProfile Labels) :=
  inferInstanceAs (SecondCountableTopology (Labels → Set.Icc (0 : ℝ) 1))

instance {Labels : Type*} : MeasurableSpace (CountableDistanceProfile Labels) := borel _
instance {Labels : Type*} : BorelSpace (CountableDistanceProfile Labels) := ⟨rfl⟩

def distanceProfilePoint {Labels Space : Type*} [PseudoMetricSpace Space]
    (births : Labels → Space) (point : Space) : CountableDistanceProfile Labels :=
  fun label => ⟨Real.exp (-dist point (births label)),
    (Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr dist_nonneg)⟩

theorem distanceProfilePoint_continuous {Labels Space : Type*} [PseudoMetricSpace Space]
    (births : Labels → Space) : Continuous (distanceProfilePoint births) := by
  apply continuous_pi
  intro label
  exact (Real.continuous_exp.comp ((continuous_id.dist continuous_const).neg)).subtype_mk _

/-- Compressing nonnegative distances by exp(-distance) is 1-Lipschitz. -/
theorem exp_neg_distance_difference_le {first last : ℝ}
    (firstNonnegative : 0 ≤ first) (lastNonnegative : 0 ≤ last) :
    |Real.exp (-first) - Real.exp (-last)| ≤ |first - last| := by
  have bound := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (f := Real.exp) (f' := Real.exp) (s := Set.Iic (0 : ℝ)) (C := 1)
    (fun value _ => (Real.hasDerivAt_exp value).hasDerivWithinAt)
    (fun value nonpositive => by
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos value)]
      exact Real.exp_le_one_iff.mpr nonpositive)
    (convex_Iic 0) (neg_nonpos.mpr lastNonnegative) (neg_nonpos.mpr firstNonnegative)
  simpa only [Real.norm_eq_abs, one_mul, neg_sub_neg, abs_sub_comm] using bound

/-- Coordinatewise uniform closeness becomes uniform metric closeness in the
fixed compact product. A single common finite coordinate set controls each
given metric tolerance; no uniformity in all infinitely many labels is assumed. -/
theorem countableDistanceProfile_uniform_of_coordinate_uniform
    {Labels : Type*} [Countable Labels] (Vertices : ℕ → Type*)
    (first last : ∀ depth, Vertices depth → CountableDistanceProfile Labels)
    (coordinateClose : ∀ label tolerance, 0 < tolerance → ∀ᶠ depth in atTop,
      ∀ vertex, dist (first depth vertex label) (last depth vertex label) < tolerance)
    (tolerance : ℝ) (tolerancePositive : 0 < tolerance) :
    ∀ᶠ depth in atTop, ∀ vertex, dist (first depth vertex) (last depth vertex) < tolerance := by
  classical
  have entourage := Metric.dist_mem_uniformity
    (α := CountableDistanceProfile Labels) tolerancePositive
  change {pair : (Labels → Set.Icc (0 : ℝ) 1) × (Labels → Set.Icc (0 : ℝ) 1) |
    @dist (CountableDistanceProfile Labels) inferInstance pair.1 pair.2 < tolerance} ∈
      𝓤 (Labels → Set.Icc (0 : ℝ) 1) at entourage
  rw [Pi.uniformity] at entourage
  obtain ⟨coordinates, entourage⟩ := (mem_iInf_finite _).mp entourage
  obtain ⟨sets, membership, equality⟩ := mem_iInf_finset.mp entourage
  have eventuallyCoordinates : ∀ᶠ depth in atTop, ∀ label ∈ coordinates,
      ∀ vertex, (first depth vertex, last depth vertex) ∈ sets label := by
    apply coordinates.eventually_all.mpr
    intro label member
    obtain ⟨coordinateSet, coordinateMember, subset⟩ := mem_comap.mp (membership label member)
    obtain ⟨coordinateTolerance, coordinatePositive, coordinateBound⟩ :=
      Metric.mem_uniformity_dist.mp coordinateMember
    filter_upwards [coordinateClose label coordinateTolerance coordinatePositive] with depth close
    intro vertex
    exact subset (coordinateBound (close vertex))
  filter_upwards [eventuallyCoordinates] with depth close
  intro vertex
  have member : (first depth vertex, last depth vertex) ∈ ⋂ label ∈ coordinates, sets label :=
    mem_iInter.mpr (fun label => mem_iInter.mpr (fun member => close label member vertex))
  rw [← equality] at member
  exact member

end
end IGSIII34.Diffusion
