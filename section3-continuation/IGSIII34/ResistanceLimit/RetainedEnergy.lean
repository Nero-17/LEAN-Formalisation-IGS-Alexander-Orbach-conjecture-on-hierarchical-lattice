import IGSIII34.ResistanceLimit.FiniteEnergy
import IGSIII.Geometry.ActualSkeletonMetric

/-!
# Energy on the actual source component

Every open edge connected to the source is retained, including edges in dangling
branches. Components not connected to the source are removed by their zero
coefficient. This is a construction on the actual finite network, rather than a
postulated resistance form.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace IGSIII34.ResistanceLimit
noncomputable section
open Universality Universality.FiniteNetwork
open scoped BigOperators

variable {vertices edges : ℕ}

def retainedConductance (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ) (edge : Fin edges) : ℝ :=
  if configuration edge = true ∧ (network.openGraph configuration).Reachable network.source (network.endpoint edge).1
    then conductance edge else 0

def retainedEnergy (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ) (potential : Fin vertices → ℝ) : ℝ :=
  finiteEnergy network.endpoint (retainedConductance network configuration conductance) potential

theorem retainedConductance_nonnegative (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ)
    (nonnegative : ∀ edge, 0 ≤ conductance edge) (edge : Fin edges) :
    0 ≤ retainedConductance network configuration conductance edge := by
  unfold retainedConductance
  split_ifs
  · exact nonnegative edge
  · exact le_rfl

theorem retainedEnergy_nonnegative (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ)
    (nonnegative : ∀ edge, 0 ≤ conductance edge) (potential : Fin vertices → ℝ) :
    0 ≤ retainedEnergy network configuration conductance potential :=
  finiteEnergy_nonnegative _ _ (retainedConductance_nonnegative network configuration conductance nonnegative) _

theorem retainedEnergy_depends_only_source_component (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ) (first second : Fin vertices → ℝ)
    (equal : ∀ vertex, (network.openGraph configuration).Reachable network.source vertex → first vertex = second vertex) :
    retainedEnergy network configuration conductance first = retainedEnergy network configuration conductance second := by
  unfold retainedEnergy finiteEnergy
  apply Finset.sum_congr rfl
  intro edge _
  by_cases retained : configuration edge = true ∧
      (network.openGraph configuration).Reachable network.source (network.endpoint edge).1
  · have adjacent : (network.openGraph configuration).Adj (network.endpoint edge).1 (network.endpoint edge).2 :=
      ⟨network.loopless edge, edge, retained.1, Or.inl rfl⟩
    rw [equal _ retained.2, equal _ (retained.2.trans adjacent.reachable)]
  · simp [retainedConductance, retained]

theorem retainedEnergy_eq_zero_of_constant (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ) (potential : Fin vertices → ℝ)
    (constant : ∀ vertex, (network.openGraph configuration).Reachable network.source vertex →
      potential vertex = potential network.source) :
    retainedEnergy network configuration conductance potential = 0 := by
  rw [retainedEnergy_depends_only_source_component network configuration conductance potential
    (fun _ => potential network.source) constant]
  exact finiteEnergy_constant _ _ _

theorem retainedEnergy_eq_zero_iff_constant (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ)
    (positive : ∀ edge, 0 < conductance edge) (potential : Fin vertices → ℝ) :
    retainedEnergy network configuration conductance potential = 0 ↔
      ∀ vertex, (network.openGraph configuration).Reachable network.source vertex →
        potential vertex = potential network.source := by
  constructor
  · intro zeroEnergy
    have edgeEquality (edge : Fin edges) (retained : configuration edge = true ∧
        (network.openGraph configuration).Reachable network.source (network.endpoint edge).1) :
        potential (network.endpoint edge).1 = potential (network.endpoint edge).2 := by
      have termNonnegative (other : Fin edges) : 0 ≤ retainedConductance network configuration conductance other *
          (potential (network.endpoint other).1 - potential (network.endpoint other).2) ^ 2 :=
        mul_nonneg (retainedConductance_nonnegative network configuration conductance
          (fun other => (positive other).le) other) (sq_nonneg _)
      have bound := Finset.single_le_sum (fun other _ => termNonnegative other) (Finset.mem_univ edge)
      change retainedConductance network configuration conductance edge *
        (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 ≤
          retainedEnergy network configuration conductance potential at bound
      rw [zeroEnergy, retainedConductance, if_pos retained] at bound
      have squareZero : (potential (network.endpoint edge).1 - potential (network.endpoint edge).2) ^ 2 = 0 := by
        nlinarith [sq_nonneg (potential (network.endpoint edge).1 - potential (network.endpoint edge).2), positive edge]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp squareZero)
    intro vertex reachable
    obtain ⟨walk⟩ := reachable
    have walkEquality : ∀ {first last : Fin vertices}, (network.openGraph configuration).Reachable network.source first →
        (walk : (network.openGraph configuration).Walk first last) → potential last = potential first := by
      intro first last firstReach walk
      induction walk with
      | nil => rfl
      | @cons first middle last adjacent tail inductionHypothesis =>
        have middleReach := firstReach.trans adjacent.reachable
        have pairEquality : potential first = potential middle := by
          rcases adjacent with ⟨_, edge, opened, orientation | orientation⟩
          · have endpointFirst := congrArg Prod.fst orientation
            have endpointSecond := congrArg Prod.snd orientation
            have retained : (network.openGraph configuration).Reachable network.source (network.endpoint edge).1 := by
              rwa [endpointFirst]
            simpa only [endpointFirst, endpointSecond] using edgeEquality edge ⟨opened, retained⟩
          · have endpointFirst := congrArg Prod.fst orientation
            have endpointSecond := congrArg Prod.snd orientation
            have retained : (network.openGraph configuration).Reachable network.source (network.endpoint edge).1 := by
              rw [endpointFirst]
              exact middleReach
            have equal : potential middle = potential first := by
              simpa only [endpointFirst, endpointSecond] using edgeEquality edge ⟨opened, retained⟩
            exact equal.symm
        exact (inductionHypothesis middleReach).trans pairEquality.symm
    exact walkEquality (SimpleGraph.Reachable.refl _) walk
  · exact retainedEnergy_eq_zero_of_constant network configuration conductance potential

theorem retainedEnergy_normal_contraction (network : Universality.FiniteNetwork vertices edges)
    (configuration : Configuration edges) (conductance : Fin edges → ℝ)
    (nonnegative : ∀ edge, 0 ≤ conductance edge) (contraction : ℝ → ℝ)
    (contracts : ∀ first second, |contraction first - contraction second| ≤ |first - second|)
    (potential : Fin vertices → ℝ) :
    retainedEnergy network configuration conductance (fun vertex => contraction (potential vertex)) ≤
      retainedEnergy network configuration conductance potential :=
  finiteEnergy_normal_contraction _ _ (retainedConductance_nonnegative network configuration conductance nonnegative)
    contraction contracts potential

end
end IGSIII34.ResistanceLimit
