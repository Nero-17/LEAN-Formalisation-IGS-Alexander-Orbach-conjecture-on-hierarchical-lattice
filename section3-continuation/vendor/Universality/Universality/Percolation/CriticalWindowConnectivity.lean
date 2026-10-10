import Universality.Percolation.CriticalWindowAtCells
import Universality.Graph.SelectedCellDistanceWindow
import Universality.Percolation.WindowNetworkEquivalence

namespace Universality.Rule
noncomputable section
open FiniteNetwork Matrix Filter
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

/-- Every fixed nondegenerate macroscopic distance window has the actual
critical mass-to-volume rate. Generation zero contains one substitution,
so its terminal-distance scale is the first power. -/
theorem Classical.critical_window_connectivity_bounds {rule : Rule} (h : rule.Classical)
    (p : ℝ) (hp : 0 < p) (hp' : p < 1) (hfixed : rule.network.reliability p = p)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) (hb : b < 1) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 < upper ∧ ∀ᶠ n : ℕ in atTop,
      lower * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal /
        (rule.edges : ℝ)) ^ (2 * n) ≤
          (rule.generation n).network.averagedWindowConnectivity p
            (a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))
            (b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1)) ∧
      (rule.generation n).network.averagedWindowConnectivity p
            (a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1))
            (b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (n + 1)) ≤
        upper * ((spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal /
          (rule.edges : ℝ)) ^ (2 * n) := by
  obtain ⟨diameter, _, hdiameter⟩ := h.generation_diameter_bound
  obtain ⟨coarse, first, second, hdistinct, hseparation, hwindow⟩ :=
    h.exists_cell_distance_window diameter hdiameter a b ha hab hb
  obtain ⟨lower, upper, hlower, hupper, hbounds⟩ :=
    h.critical_window_bounds_at_cells p hp hp' hfixed
      (rule.generation coarse).network (h.generation coarse).connected diameter hdiameter
      first second hdistinct
      (fun n => a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (coarse + n + 2))
      (fun n => b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (coarse + n + 2))
      hseparation (fun n u v => hwindow n u.val v.val)
  let rate := (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal /
    (rule.edges : ℝ)
  have hradius : 0 < (spectralRadius ℂ ((rule.network.massMatrix p).map Complex.ofReal)).toReal :=
    zero_lt_one.trans ((rule.network.interior_fixed_point_strictly_unstable p hp hp' hfixed h.scale).trans
      (rule.interior_fixed_point_spectral_dominance p hp hp' hfixed h.massAdmissible.symmetric h.scale).2.1)
  have hedges : 0 < (rule.edges : ℝ) := by
    exact_mod_cast (show 0 < rule.edges from Nat.zero_lt_of_lt h.edges_gt_one)
  have hrate : 0 < rate := div_pos hradius hedges
  refine ⟨lower / rate ^ (2 * (coarse + 1)), upper / rate ^ (2 * (coarse + 1)),
    div_pos hlower (pow_pos hrate _), div_pos hupper (pow_pos hrate _), ?_⟩
  filter_upwards [eventually_ge_atTop (coarse + 1)] with n hn
  let fine := n - (coarse + 1)
  have hindex : coarse + fine + 1 = n := by dsimp only [fine]; omega
  have hscale (constant : ℝ) : constant / rate ^ (2 * (coarse + 1)) * rate ^ (2 * n) =
      constant * rate ^ (2 * fine) := by
    have hexponent : 2 * n = 2 * (coarse + 1) + 2 * fine := by omega
    rw [hexponent, pow_add]
    field_simp
  have htransfer := (rule.generationBlockDecomposition coarse fine).averagedWindowConnectivity
    (h.generation (coarse + fine + 1)).connected p
    (a * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (coarse + fine + 2))
    (b * (rule.network.fullGraph.dist rule.network.source rule.network.target : ℝ) ^ (coarse + fine + 2))
  have hbound := hbounds fine
  rw [htransfer] at hbound
  have hsuccessor : coarse + fine + 2 = n + 1 := by omega
  rw [hindex, hsuccessor] at hbound
  change lower / rate ^ (2 * (coarse + 1)) * rate ^ (2 * n) ≤ _ ∧
    _ ≤ upper / rate ^ (2 * (coarse + 1)) * rate ^ (2 * n)
  rw [hscale, hscale]
  exact hbound

end
end Universality.Rule
