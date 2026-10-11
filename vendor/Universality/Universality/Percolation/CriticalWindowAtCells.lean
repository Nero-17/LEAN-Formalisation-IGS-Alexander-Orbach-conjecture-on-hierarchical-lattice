import Universality.Percolation.WindowPairExpectation
import Universality.Graph.GenerationVolumeBounds
import Universality.Analysis.WindowRatioBounds
import Universality.Percolation.VertexMassGrowth
import Universality.Percolation.BoundaryMassMoments
import Universality.Graph.ClassicalSubstitution

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false

/-- Actual averaged connectivity has the critical mass-to-volume rate once
two fixed coarse cells lie in the deterministic window and child diameters
lie below that window. These are purely geometric hypotheses. -/
theorem Classical.critical_window_bounds_at_cells {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    {outerVertices outerEdges : ℕ} (outer : FiniteNetwork outerVertices outerEdges)
    (houter : ∀ vertex, outer.fullGraph.Reachable outer.source vertex)
    (diameter : ℕ)
    (hdiameter : ∀ n (u v : Fin (rule.generation n).vertices),
      (rule.generation n).network.fullGraph.dist u v ≤
        diameter * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n)
    (first second : Fin outerEdges) (hdistinct : first ≠ second)
    (lowerWindow upperWindow : ℕ → ℝ)
    (hseparation : ∀ n, (diameter : ℝ) *
      (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ n < lowerWindow n)
    (hwindow : ∀ n (u v : (rule.generation n).network.InteriorVertex),
      lowerWindow n ≤ ((outer.substitute (rule.generation n).network).fullGraph.dist
        (outer.cellEmbedding (rule.generation n).network first u.val)
        (outer.cellEmbedding (rule.generation n).network second v.val) : ℝ) ∧
      ((outer.substitute (rule.generation n).network).fullGraph.dist
        (outer.cellEmbedding (rule.generation n).network first u.val)
        (outer.cellEmbedding (rule.generation n).network second v.val) : ℝ) ≤ upperWindow n) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ n : ℕ,
      lower * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal /
        (rule.edges : ℝ)) ^ (2 * n) ≤
          (outer.substitute (rule.generation n).network).averagedWindowConnectivity p (lowerWindow n) (upperWindow n) ∧
      (outer.substitute (rule.generation n).network).averagedWindowConnectivity p (lowerWindow n) (upperWindow n) ≤
        upper * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal /
          (rule.edges : ℝ)) ^ (2 * n) := by
  let radius := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal
  have hradius : 1 < radius :=
    (rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1
  have hradius0 : 0 < radius := zero_lt_one.trans hradius
  have hedges : (1 : ℝ) ≤ rule.edges := by exact_mod_cast h.edges_gt_one.le
  have hedges0 : (0 : ℝ) < rule.edges := zero_lt_one.trans_le hedges
  obtain ⟨meanLower, meanUpper, hmeanLower, _, hmeans⟩ := h.internal_vertex_mass_bounds p hp hp' hfixed
  obtain ⟨moment, hmoment, hmoments⟩ := h.internal_boundary_moment_bounds p hp hp' hfixed 2
  let volume : ℝ := (outerVertices : ℝ) + (outerEdges : ℝ) * (2 * (rule.vertices : ℝ))
  have houterVertices : (0 : ℝ) < outerVertices := by
    exact_mod_cast (show 0 < outerVertices from (by omega : 0 < 2).trans_le outer.two_le_vertices)
  have hvolume : 0 < volume := by dsimp only [volume]; positivity
  let lower : ℝ := bernoulliWeight p (fun _ : Fin outerEdges => true) * meanLower ^ 2
  let upper : ℝ := (outerVertices : ℝ) * ((outerEdges : ℝ) + 1) *
    ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) * moment) + 1
  have hlower : 0 < lower := by
    dsimp only [lower]
    exact mul_pos (bernoulliWeight_pos hp hp' _) (pow_pos hmeanLower _)
  have hupper : 0 < upper := by dsimp only [upper]; positivity
  refine ⟨lower / volume ^ 2, upper, div_pos hlower (pow_pos hvolume _), hupper, ?_⟩
  intro n
  have hpower (value : ℝ) : (value ^ n) ^ 2 = value ^ (2 * n) := by
    rw [← pow_mul, Nat.mul_comm n 2]
  have hmassScale : 0 < radius ^ (2 * n) := pow_pos hradius0 _
  have hvolumeScale : 0 < (rule.edges : ℝ) ^ (2 * n) := pow_pos hedges0 _
  have hinnerPositive : 0 < (rule.generation n).network.reliability p := by
    rwa [rule.generation_fixed_point p hfixed n]
  have hinnerLess : (rule.generation n).network.reliability p < 1 := by
    rwa [rule.generation_fixed_point p hfixed n]
  let numerator := (outer.substitute (rule.generation n).network).expectedConnectedWindowPairCount
    p (lowerWindow n) (upperWindow n)
  let denominator : ℝ := ((outer.substitute (rule.generation n).network).distanceWindowPairs
    (lowerWindow n) (upperWindow n)).card
  have hnumeratorLower : lower * radius ^ (2 * n) ≤ numerator := by
    have hraw := outer.expected_connected_window_pairs_lower (rule.generation n).network houter
      hp.le hp'.le hinnerPositive hinnerLess first second hdistinct (lowerWindow n) (upperWindow n) (hwindow n)
    rw [rule.generation_fixed_point p hfixed n] at hraw
    have hsquare := pow_le_pow_left₀ (mul_pos hmeanLower (pow_pos hradius0 n)).le (hmeans n .connected).1 2
    rw [mul_pow, hpower] at hsquare
    calc
      _ = bernoulliWeight p (fun _ : Fin outerEdges => true) * (meanLower ^ 2 * radius ^ (2 * n)) := by
        dsimp only [lower]
        ring
      _ ≤ bernoulliWeight p (fun _ : Fin outerEdges => true) *
          ((rule.generation n).network.conditionalVertexMass p .connected) ^ 2 :=
        mul_le_mul_of_nonneg_left hsquare (bernoulliWeight_nonneg hp.le hp'.le _)
      _ ≤ _ := hraw
  have hnumeratorUpper : numerator ≤ upper * radius ^ (2 * n) := by
    have hraw := outer.expectedConnectedWindowPairCount_le_boundary_second_moment
      (rule.generation n).network (h.generation n).connected
      (diameter * rule.network.fullGraph.dist rule.network.source rule.network.target ^ n)
      (hdiameter n) hp.le hp'.le (lowerWindow n) (upperWindow n) (by exact_mod_cast hseparation n)
    have hscale : (1 : ℝ) ≤ radius ^ (2 * n) := one_le_pow₀ hradius.le
    have hmomentScaled := mul_le_mul_of_nonneg_left (hmoments n) (Nat.cast_nonneg outerEdges : (0 : ℝ) ≤ _)
    have hverticesScaled := mul_le_mul_of_nonneg_left hscale (sq_nonneg (outerVertices : ℝ))
    have hsum : (outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) *
        (rule.generation n).network.expectedInternalBoundaryMoment p 2 ≤
        ((outerVertices : ℝ) ^ 2 + (outerEdges : ℝ) * moment) * radius ^ (2 * n) := by
      nlinarith
    have hmultiplied := mul_le_mul_of_nonneg_left hsum
      (show 0 ≤ (outerVertices : ℝ) * ((outerEdges : ℝ) + 1) by positivity)
    dsimp only [numerator, upper]
    nlinarith
  have hdenominatorLower : (rule.edges : ℝ) ^ (2 * n) ≤ denominator := by
    have hpair := outer.distanceWindowPairs_card_ge_two_cells (rule.generation n).network
      first second (lowerWindow n) (upperWindow n) (hwindow n)
    have hvolume := Nat.pow_le_pow_left (h.generation_volume_bounds n).1 2
    have hnat := hvolume.trans hpair
    rw [← pow_mul, Nat.mul_comm n 2] at hnat
    dsimp only [denominator]
    exact_mod_cast hnat
  have hvertices : (Fintype.card (outer.SubstitutionVertex (rule.generation n).network) : ℝ) ≤
      volume * (rule.edges : ℝ) ^ n := by
    have hinterior : (rule.generation n).vertices - 2 ≤ 2 * rule.vertices * rule.edges ^ n :=
      (Nat.sub_le _ _).trans (h.generation_volume_bounds n).2
    have hproduct := Nat.mul_le_mul_left outerEdges hinterior
    have hbase := Nat.mul_le_mul_left outerVertices
      (one_le_pow₀ (show 1 ≤ rule.edges from h.edges_gt_one.le) (n := n))
    have hnat : Fintype.card (outer.SubstitutionVertex (rule.generation n).network) ≤
        (outerVertices + outerEdges * (2 * rule.vertices)) * rule.edges ^ n := by
      rw [outer.card_substitution_vertices]
      nlinarith
    dsimp only [volume]
    exact_mod_cast hnat
  have hdenominatorUpper : denominator ≤ volume ^ 2 * (rule.edges : ℝ) ^ (2 * n) := by
    have hpair := (outer.substitute (rule.generation n).network).distanceWindowPairs_card_le_vertices_sq
      (lowerWindow n) (upperWindow n)
    have hpairReal : denominator ≤
        (Fintype.card (outer.SubstitutionVertex (rule.generation n).network) : ℝ) ^ 2 := by
      dsimp only [denominator]
      exact_mod_cast hpair
    have hsquare := pow_le_pow_left₀ (Nat.cast_nonneg _) hvertices 2
    rw [mul_pow, hpower] at hsquare
    exact hpairReal.trans hsquare
  have hb := window_ratio_bounds numerator denominator (radius ^ (2 * n))
    ((rule.edges : ℝ) ^ (2 * n)) lower upper volume hmassScale hvolumeScale hlower hupper hvolume
    hnumeratorLower hnumeratorUpper hdenominatorLower hdenominatorUpper
  simp only [(outer.substitute (rule.generation n).network).averagedWindowConnectivity_eq]
  simpa only [← div_pow, numerator, denominator, radius] using hb

end
end Universality.Rule
