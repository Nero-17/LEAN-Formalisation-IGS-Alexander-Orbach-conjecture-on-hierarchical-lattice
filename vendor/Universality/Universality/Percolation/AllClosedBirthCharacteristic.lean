import Universality.Percolation.BirthRootPointBounds
import Universality.Graph.InternalIncidentEdges

namespace Universality.FiniteNetwork
noncomputable section
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

theorem rootChildState_allClosed_eraseOrientation (R : FiniteNetwork vertices edges)
    (root : Fin vertices) (edge : Fin edges) :
    (R.rootChildState root (fun _ => false) edge).eraseOrientation =
      if edge ∈ R.incidentEdges root then some .single else none := by
  by_cases hfirst : (R.endpoint edge).1 = root
  · have hsecond : (R.endpoint edge).2 ≠ root := by
      intro heq
      exact R.loopless edge (hfirst.trans heq.symm)
    simp [rootChildState, reachableDecide_all_closed, hfirst, hsecond, Ne.symm hsecond,
      orientedStateOf, OrientedState.eraseOrientation, incidentEdges]
  · by_cases hsecond : (R.endpoint edge).2 = root
    · simp [rootChildState, reachableDecide_all_closed, hfirst, Ne.symm hfirst, hsecond,
        orientedStateOf, OrientedState.eraseOrientation, incidentEdges]
    · simp [rootChildState, reachableDecide_all_closed, hfirst, Ne.symm hfirst, hsecond, Ne.symm hsecond,
        orientedStateOf, OrientedState.eraseOrientation, incidentEdges]

theorem clusterVertices_allClosed (R : FiniteNetwork vertices edges) (root : Fin vertices) :
    R.clusterVertices (fun _ => false) root = {root} := by
  ext vertex
  simp [mem_clusterVertices, openGraph_all_closed, SimpleGraph.reachable_bot, eq_comm]

variable (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)

def conditionalCoarseRootMassProbability (p : ℝ) (root : Fin outerVertices)
    (coarse : Configuration outerEdges) (size : ℕ) : ℝ :=
  ∑ cells : Fin outerEdges → Configuration innerEdges,
    if (R.clusterVertices coarse root).card +
      ∑ edge, S.internalStateMass (R.rootChildState root coarse edge) (cells edge) = size
    then ∏ edge, S.conditionalCellWeight p (coarse edge) (cells edge) else 0

def conditionalCoarseRootCharacteristic (p : ℝ) (root : Fin outerVertices)
    (coarse : Configuration outerEdges) (t : ℝ) : ℂ :=
  ∑ cells : Fin outerEdges → Configuration innerEdges,
    (∏ edge, (S.conditionalCellWeight p (coarse edge) (cells edge) : ℂ)) *
      Complex.exp ((t * ((R.clusterVertices coarse root).card +
        ∑ edge, S.internalStateMass (R.rootChildState root coarse edge) (cells edge)) : ℝ) * Complex.I)

theorem conditionalCoarseRootCharacteristic_product (p : ℝ) (root : Fin outerVertices)
    (coarse : Configuration outerEdges) (t : ℝ) :
    R.conditionalCoarseRootCharacteristic S p root coarse t =
      Complex.exp ((t * (R.clusterVertices coarse root).card : ℝ) * Complex.I) *
        ∏ edge, S.conditionalInternalCharacteristic p (coarse edge)
          (R.rootChildState root coarse edge).sourceSelected
          (R.rootChildState root coarse edge).targetSelected t := by
  unfold conditionalCoarseRootCharacteristic
  have hexp (cells : Fin outerEdges → Configuration innerEdges) :
      Complex.exp ((t * ((R.clusterVertices coarse root).card +
        ∑ edge, S.internalStateMass (R.rootChildState root coarse edge) (cells edge)) : ℝ) * Complex.I) =
      Complex.exp ((t * (R.clusterVertices coarse root).card : ℝ) * Complex.I) *
        ∏ edge, Complex.exp ((t * S.internalStateMass (R.rootChildState root coarse edge) (cells edge) : ℝ) * Complex.I) := by
    simp only [Nat.cast_add, Nat.cast_sum, mul_add, Complex.ofReal_add, add_mul,
      Complex.exp_add, Finset.mul_sum, Complex.ofReal_sum, Finset.sum_mul, Complex.exp_sum]
  simp_rw [hexp]
  have hfactor (cells : Fin outerEdges → Configuration innerEdges) :
      (∏ edge, (S.conditionalCellWeight p (coarse edge) (cells edge) : ℂ)) *
        (Complex.exp ((t * (R.clusterVertices coarse root).card : ℝ) * Complex.I) *
          ∏ edge, Complex.exp ((t * S.internalStateMass (R.rootChildState root coarse edge) (cells edge) : ℝ) * Complex.I)) =
      Complex.exp ((t * (R.clusterVertices coarse root).card : ℝ) * Complex.I) *
        ∏ edge, (S.conditionalCellWeight p (coarse edge) (cells edge) : ℂ) *
          Complex.exp ((t * S.internalStateMass (R.rootChildState root coarse edge) (cells edge) : ℝ) * Complex.I) := by
    rw [Finset.prod_mul_distrib]
    ring
  simp_rw [hfactor]
  rw [← Finset.mul_sum]
  congr 1
  simpa only [internalStateMass, conditionalInternalCharacteristic] using (Fintype.prod_sum
    (fun edge cell => (S.conditionalCellWeight p (coarse edge) cell : ℂ) *
      Complex.exp ((t * S.internalStateMass (R.rootChildState root coarse edge) cell : ℝ) * Complex.I))).symm

theorem allClosed_coarseRoot_characteristic
    (symmetry : S.NetworkSymmetry)
    (hs : symmetry.vertex S.source = S.target) (ht : symmetry.vertex S.target = S.source)
    (p : ℝ) (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (root : Fin outerVertices) (t : ℝ) :
    R.conditionalCoarseRootCharacteristic S p root (fun _ => false) t =
      Complex.exp ((t : ℂ) * Complex.I) *
        S.conditionalVertexCharacteristic p .single t ^ (R.incidentEdges root).card := by
  rw [R.conditionalCoarseRootCharacteristic_product S, R.clusterVertices_allClosed]
  simp only [Finset.card_singleton, Nat.cast_one, mul_one]
  congr 1
  have hfactor (edge : Fin outerEdges) :
      S.conditionalInternalCharacteristic p false
        (R.rootChildState root (fun _ => false) edge).sourceSelected
        (R.rootChildState root (fun _ => false) edge).targetSelected t =
      if edge ∈ R.incidentEdges root then S.conditionalVertexCharacteristic p .single t else 1 := by
    rw [S.conditionalInternalCharacteristic_oriented symmetry hs ht p hpositive hless _ false t
      (fun hlive => R.live_rootChildState_determines_crossing root (fun _ => false) edge hlive),
      R.rootChildState_allClosed_eraseOrientation]
    split_ifs <;> rfl
  simp_rw [hfactor]
  rw [Finset.prod_ite_mem_eq, Finset.prod_const]

theorem expectedBirthClusterCount_ge_allClosed_root
    {p : ℝ} (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hpositive : 0 < S.reliability p) (hless : S.reliability p < 1)
    (root : R.InteriorVertex) (size : ℕ) :
    bernoulliWeight (S.reliability p) (fun _ : Fin outerEdges => false) *
      R.conditionalCoarseRootMassProbability S p root.val (fun _ => false) size ≤
        R.expectedBirthClusterCount S p size := by
  have hroot : R.source ∉ R.clusterVertices (fun _ => false) root.val ∧
      R.target ∉ R.clusterVertices (fun _ => false) root.val := by
    simp [R.clusterVertices_allClosed, root.property.1, root.property.2,
      Ne.symm root.property.1, Ne.symm root.property.2]
  simpa only [conditionalCoarseRootMassProbability, mul_ite, mul_one, mul_zero] using
    R.expectedBirthClusterCount_ge_coarseRoot_branch S hp hp' hpositive hless (fun _ => false) root.val hroot size

end
end Universality.FiniteNetwork

