import Universality.Percolation.MultilevelLaw
import Universality.Percolation.ClusterMass

namespace Universality.FiniteNetwork
noncomputable section

/-- The two one-terminal states stay distinct until terminal symmetry is used. -/
inductive OrientedState where
  | connected | both | sourceOnly | targetOnly | inactive
  deriving DecidableEq, Fintype

def orientedStateOf (sourceActive targetActive opened : Bool) : OrientedState :=
  if sourceActive then
    if targetActive then (if opened then .connected else .both) else .sourceOnly
  else if targetActive then .targetOnly else .inactive

def OrientedState.sourceSelected : OrientedState → Bool
  | .connected | .both | .sourceOnly => true
  | .targetOnly | .inactive => false

def OrientedState.targetSelected : OrientedState → Bool
  | .connected | .both | .targetOnly => true
  | .sourceOnly | .inactive => false

def OrientedState.eraseOrientation : OrientedState → Option LiveState
  | .connected => some .connected
  | .both => some .both
  | .sourceOnly | .targetOnly => some .single
  | .inactive => none

theorem orientedStateOf_sourceSelected (a b opened : Bool) :
    (orientedStateOf a b opened).sourceSelected = a := by
  cases a <;> cases b <;> cases opened <;> rfl

theorem orientedStateOf_targetSelected (a b opened : Bool) :
    (orientedStateOf a b opened).targetSelected = b := by
  cases a <;> cases b <;> cases opened <;> rfl

variable {vertices edges outerVertices outerEdges innerVertices innerEdges : ℕ}

def selectedActive (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) (v : Fin vertices) : Bool :=
  (sourceSelected && (R.openGraph ω).reachableDecide R.source v) ||
    (targetSelected && (R.openGraph ω).reachableDecide R.target v)

def orientedChildState (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) (e : Fin edges) :
    OrientedState :=
  orientedStateOf
    (R.selectedActive sourceSelected targetSelected ω (R.endpoint e).1)
    (R.selectedActive sourceSelected targetSelected ω (R.endpoint e).2) (ω e)

theorem eraseOrientation_orientedChildState (R : FiniteNetwork vertices edges)
    (σ : LiveState) (ω : Configuration edges) (e : Fin edges) :
    (R.orientedChildState true (σ == .both) ω e).eraseOrientation = R.childState σ ω e := by
  have hactive (v : Fin vertices) :
      R.selectedActive true (σ == .both) ω v = R.active σ ω v := by
    simp [selectedActive, active]
  simp only [orientedChildState, hactive, childState]
  cases R.active σ ω (R.endpoint e).1 <;> cases R.active σ ω (R.endpoint e).2 <;>
    cases ω e <;> rfl

theorem selectedActive_substitute_cell
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (sourceSelected targetSelected : Bool) (ω : Fin outerEdges → Configuration innerEdges)
    (e : Fin outerEdges) (x : Fin innerVertices) :
    (R.substitute S).selectedActive sourceSelected targetSelected
      (substitutionConfigurationEquiv ω) (Fintype.equivFin _ (R.cellVertex S e x)) =
      S.selectedActive
        (R.selectedActive sourceSelected targetSelected (S.coarseConfiguration ω) (R.endpoint e).1)
        (R.selectedActive sourceSelected targetSelected (S.coarseConfiguration ω) (R.endpoint e).2)
        (ω e) x := by
  apply Bool.eq_iff_iff.mpr
  simp only [selectedActive, Bool.or_eq_true, Bool.and_eq_true,
    SimpleGraph.reachableDecide_eq_true]
  change
    ((sourceSelected = true ∧
      ((R.substitute S).openGraph (substitutionConfigurationEquiv ω)).Reachable
        (Fintype.equivFin _ (Sum.inl R.source)) (Fintype.equivFin _ (R.cellVertex S e x))) ∨
     (targetSelected = true ∧
      ((R.substitute S).openGraph (substitutionConfigurationEquiv ω)).Reachable
        (Fintype.equivFin _ (Sum.inl R.target)) (Fintype.equivFin _ (R.cellVertex S e x)))) ↔ _
  simp only [R.substitute_reachable_iff S, R.substitutedReachable_iff_active S,
    R.substitutionActive_cell S]
  tauto

/-- Pathwise refinement retains which endpoint is active. This identity is
pointwise in the entire cell configuration, before taking probabilities. -/
theorem orientedChildState_substitute
    (R : FiniteNetwork outerVertices outerEdges) (S : FiniteNetwork innerVertices innerEdges)
    (sourceSelected targetSelected : Bool) (ω : Fin outerEdges → Configuration innerEdges)
    (e : Fin outerEdges) (f : Fin innerEdges) :
    (R.substitute S).orientedChildState sourceSelected targetSelected
      (substitutionConfigurationEquiv ω) (finProdFinEquiv (e, f)) =
      S.orientedChildState
        (R.orientedChildState sourceSelected targetSelected (S.coarseConfiguration ω) e).sourceSelected
        (R.orientedChildState sourceSelected targetSelected (S.coarseConfiguration ω) e).targetSelected
        (ω e) f := by
  unfold orientedChildState
  rw [orientedStateOf_sourceSelected, orientedStateOf_targetSelected,
    R.substitute_endpoint S, R.selectedActive_substitute_cell S,
    R.selectedActive_substitute_cell S]
  have hω : substitutionConfigurationEquiv ω (finProdFinEquiv (e, f)) = ω e f := by
    change ω (finProdFinEquiv.symm (finProdFinEquiv (e, f))).1
      (finProdFinEquiv.symm (finProdFinEquiv (e, f))).2 = ω e f
    rw [Equiv.symm_apply_apply]
  rw [hω]

theorem selectedActive_endpoints_eq_of_open (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) (e : Fin edges)
    (hopen : ω e = true) :
    R.selectedActive sourceSelected targetSelected ω (R.endpoint e).1 =
      R.selectedActive sourceSelected targetSelected ω (R.endpoint e).2 := by
  have hadj : (R.openGraph ω).Adj (R.endpoint e).1 (R.endpoint e).2 :=
    ⟨R.loopless e, e, hopen, Or.inl rfl⟩
  have hreach (root : Fin vertices) :
      (R.openGraph ω).reachableDecide root (R.endpoint e).1 =
        (R.openGraph ω).reachableDecide root (R.endpoint e).2 := by
    apply Bool.eq_iff_iff.mpr
    simp only [SimpleGraph.reachableDecide_eq_true]
    exact ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
  simp only [selectedActive, hreach]

theorem orientedChildState_connected_iff (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) (e : Fin edges) :
    R.orientedChildState sourceSelected targetSelected ω e = .connected ↔
      ω e = true ∧ R.selectedActive sourceSelected targetSelected ω (R.endpoint e).1 = true := by
  by_cases hopen : ω e = true
  · have hactive := R.selectedActive_endpoints_eq_of_open sourceSelected targetSelected ω e hopen
    simp only [orientedChildState, orientedStateOf, hopen, ← hactive]
    cases R.selectedActive sourceSelected targetSelected ω (R.endpoint e).1 <;> simp
  · have hclosed : ω e = false := Bool.eq_false_iff.mpr hopen
    simp only [orientedChildState, orientedStateOf, hclosed]
    cases R.selectedActive sourceSelected targetSelected ω (R.endpoint e).1 <;>
      cases R.selectedActive sourceSelected targetSelected ω (R.endpoint e).2 <;> simp

/-- At the final level the connected labels extract precisely the actual
open edges in the source cluster, including attached branches. -/
theorem oriented_cluster_extraction (R : FiniteNetwork vertices edges)
    (ω : Configuration edges) (e : Fin edges) :
    R.orientedChildState true false ω e = .connected ↔
      ω e = true ∧ (R.openGraph ω).Reachable R.source (R.endpoint e).1 := by
  rw [R.orientedChildState_connected_iff]
  simp [selectedActive, SimpleGraph.reachableDecide_eq_true]

theorem inactive_has_no_live_children (R : FiniteNetwork vertices edges)
    (ω : Configuration edges) (e : Fin edges) :
    R.orientedChildState false false ω e = .inactive := by
  simp [orientedChildState, selectedActive, orientedStateOf]

/-- On a live child the coarse crossing bit is determined by its oriented
state. Thus the product conditional laws really are the c/b/u parent laws. -/
theorem live_oriented_state_determines_crossing (R : FiniteNetwork vertices edges)
    (sourceSelected targetSelected : Bool) (ω : Configuration edges) (e : Fin edges)
    (hlive : R.orientedChildState sourceSelected targetSelected ω e ≠ .inactive) :
    (R.orientedChildState sourceSelected targetSelected ω e = .connected ↔ ω e = true) := by
  rw [R.orientedChildState_connected_iff]
  constructor
  · exact And.left
  · intro hopen
    refine ⟨hopen, ?_⟩
    have hactive := R.selectedActive_endpoints_eq_of_open sourceSelected targetSelected ω e hopen
    unfold orientedChildState orientedStateOf at hlive
    rw [← hactive, hopen] at hlive
    cases ha : R.selectedActive sourceSelected targetSelected ω (R.endpoint e).1
    · simp [ha] at hlive
    · rfl

/-- Terminal symmetry preserves the whole conditioned configuration law,
not just a conditional first moment. The symmetry's vertex map exchanges
the terminal orientation when its terminal-swap hypotheses are supplied. -/
theorem NetworkSymmetry.conditionalCellWeight (R : FiniteNetwork vertices edges)
    (symmetry : R.NetworkSymmetry)
    (hs : symmetry.vertex R.source = R.target) (ht : symmetry.vertex R.target = R.source)
    (p : ℝ) (opened : Bool) (ω : Configuration edges) :
    R.conditionalCellWeight p opened (symmetry.configurationEquiv ω) =
      R.conditionalCellWeight p opened ω := by
  unfold FiniteNetwork.conditionalCellWeight
  rw [symmetry.crosses_configuration_of_terminal_swap hs ht,
    symmetry.bernoulliWeight_configuration]

end
end Universality.FiniteNetwork
