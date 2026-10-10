import IGSIII34.Topology.VendorBrouwer
import Mathlib.Analysis.Convex.PartitionOfUnity
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Algebra.Module.LocallyConvex

set_option autoImplicit false

namespace IGSIII34.Topology
noncomputable section
open Set Filter Topology

variable {Space : Type*} [AddCommGroup Space] [Module ℝ Space] [TopologicalSpace Space]
  [IsTopologicalAddGroup Space] [ContinuousSMul ℝ Space] [T2Space Space]

theorem approximate_fixedPoint_of_partition {Index : Type*} [Fintype Index]
    [DecidableEq Index] [Nonempty Index] {domain : Set Space}
    (domainConvex : Convex ℝ domain) (map : C(domain, domain))
    (centers : Index → domain) (weights : Index → C(domain, ℝ))
    (weightsNonnegative : ∀ index point, 0 ≤ weights index point)
    (weightsSum : ∀ point, ∑ index, weights index point = 1)
    {neighborhood : Set Space} (neighborhoodConvex : Convex ℝ neighborhood)
    (supported : ∀ point index, weights index point ≠ 0 →
      (map (centers index)).val - (map point).val ∈ neighborhood) :
    ∃ point : domain, point.val - (map point).val ∈ neighborhood := by
  let interpolation : stdSimplex ℝ Index → domain := fun coefficients =>
    ⟨∑ index, coefficients.val index • (map (centers index)).val,
      domainConvex.sum_mem (fun index _ => coefficients.property.1 index)
        coefficients.property.2 (fun index _ => (map (centers index)).property)⟩
  have interpolationContinuous : Continuous interpolation := by
    apply Continuous.subtype_mk
    exact continuous_finsetSum _ (fun index _ =>
      ((continuous_apply index).comp continuous_subtype_val).smul continuous_const)
  let coefficientMap : C(stdSimplex ℝ Index, stdSimplex ℝ Index) :=
    ⟨fun coefficients => ⟨fun index => weights index (interpolation coefficients),
        ⟨fun index => weightsNonnegative index _, weightsSum _⟩⟩,
      (continuous_pi (fun index => (weights index).continuous.comp interpolationContinuous)).subtype_mk _⟩
  have simplexNonempty : (stdSimplex ℝ Index).Nonempty := by
    obtain ⟨index⟩ := ‹Nonempty Index›
    exact ⟨Pi.single index 1, single_mem_stdSimplex ℝ index⟩
  obtain ⟨coefficients, fixed⟩ := Vendor.brouwer_fixed_point (stdSimplex ℝ Index)
    (convex_stdSimplex ℝ Index) (isCompact_stdSimplex ℝ Index) simplexNonempty coefficientMap
  let point : domain := interpolation coefficients
  have coordinates (index : Index) : weights index point = coefficients.val index :=
    congrArg (fun value : stdSimplex ℝ Index => value.val index) fixed
  have representation : point.val = ∑ index, weights index point • (map (centers index)).val := by
    simp only [coordinates]
    rfl
  have convexCombination := neighborhoodConvex.finsum_mem
    (fun index => weightsNonnegative index point)
    (by simpa only [finsum_eq_sum_of_fintype] using weightsSum point)
    (supported point)
  rw [finsum_eq_sum_of_fintype] at convexCombination
  have differenceIdentity :
      (∑ index, weights index point • ((map (centers index)).val - (map point).val)) =
        point.val - (map point).val := by
    simp_rw [smul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_smul, weightsSum, one_smul, ← representation]
  exact ⟨point, differenceIdentity ▸ convexCombination⟩

theorem approximate_fixedPoint {domain : Set Space} (domainConvex : Convex ℝ domain)
    (domainCompact : IsCompact domain) (domainNonempty : domain.Nonempty)
    (map : C(domain, domain)) {neighborhood : Set Space}
    (containsZero : (0 : Space) ∈ neighborhood) (neighborhoodOpen : IsOpen neighborhood)
    (neighborhoodConvex : Convex ℝ neighborhood) :
    ∃ point : domain, point.val - (map point).val ∈ neighborhood := by
  classical
  letI : CompactSpace domain := isCompact_iff_compactSpace.mp domainCompact
  letI : Nonempty domain := Set.nonempty_coe_sort.mpr domainNonempty
  let cover : domain → Set domain := fun center =>
    {point | (map center).val - (map point).val ∈ neighborhood}
  have coverOpen (center : domain) : IsOpen (cover center) :=
    neighborhoodOpen.preimage (continuous_const.sub (continuous_subtype_val.comp map.continuous))
  have covers : (Set.univ : Set domain) ⊆ ⋃ center, cover center := by
    intro point _
    exact Set.mem_iUnion.mpr ⟨point, by simpa only [cover, sub_self, Set.mem_setOf_eq] using containsZero⟩
  obtain ⟨finiteCenters, finiteCover⟩ := isCompact_univ.elim_finite_subcover cover coverOpen covers
  have finiteCentersNonempty : finiteCenters.Nonempty := by
    obtain ⟨point⟩ := ‹Nonempty domain›
    obtain ⟨center, membership, _⟩ := Set.mem_iUnion₂.mp (finiteCover (Set.mem_univ point))
    exact ⟨center, membership⟩
  letI : Nonempty {center // center ∈ finiteCenters} := by
    obtain ⟨center, membership⟩ := finiteCentersNonempty
    exact ⟨⟨center, membership⟩⟩
  have finiteCover' : (Set.univ : Set domain) ⊆
      ⋃ center : {center // center ∈ finiteCenters}, cover center.val := by
    intro point _
    obtain ⟨center, membership, covered⟩ := Set.mem_iUnion₂.mp (finiteCover (Set.mem_univ point))
    exact Set.mem_iUnion.mpr ⟨⟨center, membership⟩, covered⟩
  obtain ⟨partition, subordinate, _⟩ :=
    PartitionOfUnity.exists_isSubordinate_of_locallyFinite_t2space isCompact_univ
      (fun center : {center // center ∈ finiteCenters} => cover center.val)
      (fun center => coverOpen center.val) (locallyFinite_of_finite _) finiteCover'
  exact approximate_fixedPoint_of_partition domainConvex map
    (fun center : {center // center ∈ finiteCenters} => center.val)
    (fun index => partition index) (fun index point => partition.nonneg index point)
    (fun point => by simpa only [finsum_eq_sum_of_fintype] using partition.sum_eq_one (Set.mem_univ point))
    neighborhoodConvex (fun point index nonzero => subordinate index (subset_closure nonzero))

theorem schauder_fixed_point [LocallyConvexSpace ℝ Space]
    {domain : Set Space} (domainConvex : Convex ℝ domain)
    (domainCompact : IsCompact domain) (domainNonempty : domain.Nonempty)
    (map : C(domain, domain)) : ∃ point, map point = point := by
  letI : CompactSpace domain := isCompact_iff_compactSpace.mp domainCompact
  let defect : domain → Space := fun point => point.val - (map point).val
  have defectContinuous : Continuous defect :=
    continuous_subtype_val.sub (continuous_subtype_val.comp map.continuous)
  have defectClosed : IsClosed (Set.range defect) :=
    (isCompact_range defectContinuous).isClosed
  have zeroInClosure : (0 : Space) ∈ closure (Set.range defect) := by
    rw [mem_closure_iff_nhds]
    intro neighborhood neighborhoodMember
    obtain ⟨smaller, properties, subset⟩ :=
      (LocallyConvexSpace.convex_open_basis_zero ℝ Space).mem_iff.mp neighborhoodMember
    obtain ⟨point, near⟩ := approximate_fixedPoint domainConvex domainCompact domainNonempty map
      properties.1 properties.2.1 properties.2.2
    exact ⟨defect point, subset near, ⟨point, rfl⟩⟩
  rw [defectClosed.closure_eq] at zeroInClosure
  obtain ⟨point, zero⟩ := zeroInClosure
  refine ⟨point, Subtype.ext ?_⟩
  exact (sub_eq_zero.mp zero).symm

end
end IGSIII34.Topology
