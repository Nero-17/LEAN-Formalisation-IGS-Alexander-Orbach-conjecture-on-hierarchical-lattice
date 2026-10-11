import IGSIII34.Spectral.CompactEigenbasisCompletion20261011

/-! Only finitely many vectors of a compact operator's orthonormal eigenfamily
can have eigenvalue bounded away from zero. The proof uses an actual finite
cover of the compact image of the unit ball. -/
set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace IGSIII34.Spectral
noncomputable section
open Filter
open scoped Topology

theorem finite_index_of_compact_separated_image_completion20261011
    {Index Space : Type*} [MetricSpace Space]
    (image : Index → Space) (carrier : Set Space) (compact : IsCompact carrier)
    (inside : ∀ index, image index ∈ carrier)
    (radius : ℝ) (positive : 0 < radius)
    (separated : ∀ first second, first ≠ second → radius ≤ dist (image first) (image second)) :
    Finite Index := by
  classical
  obtain ⟨centers, finite, covers⟩ := Metric.totallyBounded_iff.mp compact.totallyBounded
    (radius / 3) (by positivity)
  have centerExists (index : Index) : ∃ center : centers, dist (image index) center.val < radius / 3 := by
    obtain ⟨center, member, close⟩ := Set.mem_iUnion₂.mp (covers (inside index))
    exact ⟨⟨center, member⟩, by simpa only [Metric.mem_ball, dist_comm] using close⟩
  choose center close using centerExists
  letI : Fintype centers := finite.fintype
  apply Finite.of_injective center
  intro first second equality
  by_contra different
  have triangle := dist_triangle (image first) (center first).val (image second)
  have secondClose : dist (center first).val (image second) < radius / 3 := by
    rw [equality, dist_comm]
    exact close second
  nlinarith [separated first second different, close first]

theorem compact_orthonormal_eigenvalues_finite_large_completion20261011
    {Hilbert Index : Type*} [NormedAddCommGroup Hilbert] [InnerProductSpace ℝ Hilbert]
    [CompleteSpace Hilbert] (operator : Hilbert →L[ℝ] Hilbert)
    (compact : IsCompactOperator operator) (vectors : Index → Hilbert)
    (orthonormal : Orthonormal ℝ vectors) (eigenvalues : Index → ℝ)
    (eigenvectors : ∀ index, operator (vectors index) = eigenvalues index • vectors index)
    (radius : ℝ) (positive : 0 < radius) :
    {index | radius ≤ |eigenvalues index|}.Finite := by
  classical
  let large : Set Index := {index | radius ≤ |eigenvalues index|}
  let images : large → Hilbert := fun index => operator (vectors index.val)
  have compactImage : IsCompact (closure (operator '' Metric.closedBall 0 1)) :=
    compact.isCompact_closure_image_of_bounded Metric.isBounded_closedBall
  have inside (index : large) : images index ∈ closure (operator '' Metric.closedBall 0 1) := by
    apply subset_closure
    exact ⟨vectors index.val, by simp [orthonormal.norm_eq_one], rfl⟩
  have separated (first second : large) (different : first ≠ second) :
      radius ≤ dist (images first) (images second) := by
    have valuesDifferent : first.val ≠ second.val := Subtype.val_injective.ne different
    have innerZero := orthonormal.inner_eq_zero valuesDifferent
    have square : ‖images first - images second‖ ^ 2 =
        eigenvalues first.val ^ 2 + eigenvalues second.val ^ 2 := by
      change ‖operator (vectors first.val) - operator (vectors second.val)‖ ^ 2 = _
      rw [eigenvectors first.val, eigenvectors second.val, norm_sub_sq_real,
        norm_smul, norm_smul, orthonormal.norm_eq_one, orthonormal.norm_eq_one]
      simp only [inner_smul_left, inner_smul_right, innerZero, mul_zero, sub_zero,
        Real.norm_eq_abs, mul_one, sq_abs]
    rw [dist_eq_norm]
    have firstBound : radius ≤ |eigenvalues first.val| := first.property
    have secondBound : radius ≤ |eigenvalues second.val| := second.property
    nlinarith [sq_abs (eigenvalues first.val), sq_abs (eigenvalues second.val),
      abs_nonneg (eigenvalues first.val), abs_nonneg (eigenvalues second.val),
      norm_nonneg (images first - images second)]
  letI : Finite large := finite_index_of_compact_separated_image_completion20261011
    images _ compactImage inside radius positive separated
  exact Set.toFinite large

end
end IGSIII34.Spectral
