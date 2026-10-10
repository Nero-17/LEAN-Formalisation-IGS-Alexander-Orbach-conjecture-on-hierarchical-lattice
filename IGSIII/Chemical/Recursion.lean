import IGSIII.Chemical.PathFunctional

set_option autoImplicit false

/-!
# Deterministic chemical recursion on an address tree

Addresses are lists of edges. Each address carries a finite nonempty family of
path edge sets. The recursion evaluates shortest-path costs from the leaves
upwards. We prove comparison, scaling, depth bounds, successive-depth bounds,
and the exact formula when all retained paths have the same cardinality.

This module does not construct a substituted graph or a percolation cluster.
In particular, identifying this recursion with the graph distance of the
paper's full terminal-connected cluster remains a separate graph-theoretic
bridge. No probabilistic convergence or random eigenlaw is asserted here.
-/

namespace IGSIII.Chemical

variable {Edge : Type*} [DecidableEq Edge]

/-- Evaluate an address-dependent terminal cost through a finite depth of the
shortest-path recursion. -/
noncomputable def treeCost (family : List Edge → PathFamily Edge)
    (leafCost : List Edge → ℝ) (address : List Edge) : ℕ → ℝ
  | 0 => leafCost address
  | depth + 1 => (family address).shortest
      (fun edge => treeCost family leafCost (address ++ [edge]) depth)

@[simp] theorem treeCost_zero (family : List Edge → PathFamily Edge)
    (leafCost : List Edge → ℝ) (address : List Edge) :
    treeCost family leafCost address 0 = leafCost address := rfl

@[simp] theorem treeCost_succ (family : List Edge → PathFamily Edge)
    (leafCost : List Edge → ℝ) (address : List Edge) (depth : ℕ) :
    treeCost family leafCost address (depth + 1) =
      (family address).shortest
        (fun edge => treeCost family leafCost (address ++ [edge]) depth) := rfl

/-- Coordinatewise comparison of the leaf costs survives every finite depth. -/
theorem treeCost_mono (family : List Edge → PathFamily Edge)
    {first second : List Edge → ℝ} (comparison : ∀ address, first address ≤ second address)
    (address : List Edge) (depth : ℕ) :
    treeCost family first address depth ≤ treeCost family second address depth := by
  induction depth generalizing address with
  | zero => exact comparison address
  | succ depth inductionHypothesis =>
      exact (family address).shortest_mono
        (fun edge => inductionHypothesis (address ++ [edge]))

/-- A common nonnegative scalar can be passed through the whole recursion. -/
theorem treeCost_scale (family : List Edge → PathFamily Edge)
    (leafCost : List Edge → ℝ) {scalar : ℝ} (nonnegative : 0 ≤ scalar)
    (address : List Edge) (depth : ℕ) :
    treeCost family (fun descendant => scalar * leafCost descendant) address depth =
      scalar * treeCost family leafCost address depth := by
  induction depth generalizing address with
  | zero => rfl
  | succ depth inductionHypothesis =>
      simp only [treeCost_succ, inductionHypothesis]
      exact (family address).shortest_scale _ nonnegative

theorem treeCost_nonneg (family : List Edge → PathFamily Edge)
    {leafCost : List Edge → ℝ} (nonnegative : ∀ address, 0 ≤ leafCost address)
    (address : List Edge) (depth : ℕ) :
    0 ≤ treeCost family leafCost address depth := by
  induction depth generalizing address with
  | zero => exact nonnegative address
  | succ depth inductionHypothesis =>
      exact (family address).shortest_nonneg
        (fun edge => inductionHypothesis (address ++ [edge]))

/-- The deterministic terminal-distance recursion with unit terminal costs. -/
noncomputable def terminalDistance (family : List Edge → PathFamily Edge)
    (address : List Edge) (depth : ℕ) : ℝ :=
  treeCost family (fun _ => 1) address depth

@[simp] theorem terminalDistance_zero (family : List Edge → PathFamily Edge)
    (address : List Edge) : terminalDistance family address 0 = 1 := rfl

@[simp] theorem terminalDistance_succ (family : List Edge → PathFamily Edge)
    (address : List Edge) (depth : ℕ) :
    terminalDistance family address (depth + 1) =
      (family address).shortest
        (fun edge => terminalDistance family (address ++ [edge]) depth) := rfl

theorem terminalDistance_nonneg (family : List Edge → PathFamily Edge)
    (address : List Edge) (depth : ℕ) :
    0 ≤ terminalDistance family address depth :=
  treeCost_nonneg family (fun _ => zero_le_one) address depth

namespace PathFamily

theorem shortest_one_lower (family : PathFamily Edge) {lower : ℝ}
    (cardLower : ∀ path ∈ family.paths, lower ≤ (path.card : ℝ)) :
    lower ≤ family.shortest (fun _ => 1) := by
  apply family.le_shortest
  intro path membership
  simpa [pathCost] using cardLower path membership

theorem shortest_one_upper (family : PathFamily Edge) {upper : ℝ}
    (cardUpper : ∀ path ∈ family.paths, (path.card : ℝ) ≤ upper) :
    family.shortest (fun _ => 1) ≤ upper := by
  obtain ⟨path, membership⟩ := family.nonempty
  calc
    family.shortest (fun _ => 1) ≤ pathCost path (fun _ => 1) :=
      family.shortest_le_pathCost _ membership
    _ = (path.card : ℝ) := by simp [pathCost]
    _ ≤ upper := cardUpper path membership

end PathFamily

/-- Uniform path-cardinality lower bounds imply a lower growth bound for one
additional generation. The induction quantifies over every address. -/
theorem lower_mul_terminalDistance_le_succ
    (family : List Edge → PathFamily Edge) {lower : ℝ} (nonnegative : 0 ≤ lower)
    (cardLower : ∀ address path, path ∈ (family address).paths → lower ≤ (path.card : ℝ))
    (address : List Edge) (depth : ℕ) :
    lower * terminalDistance family address depth ≤
      terminalDistance family address (depth + 1) := by
  induction depth generalizing address with
  | zero =>
      simpa using (family address).shortest_one_lower (cardLower address)
  | succ depth inductionHypothesis =>
      calc
        lower * terminalDistance family address (depth + 1) =
            (family address).shortest
              (fun edge => lower * terminalDistance family (address ++ [edge]) depth) := by
          rw [(family address).shortest_scale _ nonnegative]
          rfl
        _ ≤ (family address).shortest
              (fun edge => terminalDistance family (address ++ [edge]) (depth + 1)) :=
          (family address).shortest_mono
            (fun edge => inductionHypothesis (address ++ [edge]))
        _ = terminalDistance family address (depth + 1 + 1) := rfl

/-- Uniform path-cardinality upper bounds imply an upper growth bound for one
additional generation. -/
theorem terminalDistance_succ_le_upper_mul
    (family : List Edge → PathFamily Edge) {upper : ℝ} (nonnegative : 0 ≤ upper)
    (cardUpper : ∀ address path, path ∈ (family address).paths → (path.card : ℝ) ≤ upper)
    (address : List Edge) (depth : ℕ) :
    terminalDistance family address (depth + 1) ≤
      upper * terminalDistance family address depth := by
  induction depth generalizing address with
  | zero =>
      simpa using (family address).shortest_one_upper (cardUpper address)
  | succ depth inductionHypothesis =>
      calc
        terminalDistance family address (depth + 1 + 1) =
            (family address).shortest
              (fun edge => terminalDistance family (address ++ [edge]) (depth + 1)) := rfl
        _ ≤ (family address).shortest
              (fun edge => upper * terminalDistance family (address ++ [edge]) depth) :=
          (family address).shortest_mono
            (fun edge => inductionHypothesis (address ++ [edge]))
        _ = upper * terminalDistance family address (depth + 1) := by
          rw [(family address).shortest_scale _ nonnegative]
          rfl

theorem lower_pow_le_terminalDistance
    (family : List Edge → PathFamily Edge) {lower : ℝ} (nonnegative : 0 ≤ lower)
    (cardLower : ∀ address path, path ∈ (family address).paths → lower ≤ (path.card : ℝ))
    (address : List Edge) (depth : ℕ) :
    lower ^ depth ≤ terminalDistance family address depth := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      calc
        lower ^ (depth + 1) = lower * lower ^ depth := by rw [pow_succ]; ring
        _ ≤ lower * terminalDistance family address depth :=
          mul_le_mul_of_nonneg_left inductionHypothesis nonnegative
        _ ≤ terminalDistance family address (depth + 1) :=
          lower_mul_terminalDistance_le_succ family nonnegative cardLower address depth

theorem terminalDistance_le_upper_pow
    (family : List Edge → PathFamily Edge) {upper : ℝ} (nonnegative : 0 ≤ upper)
    (cardUpper : ∀ address path, path ∈ (family address).paths → (path.card : ℝ) ≤ upper)
    (address : List Edge) (depth : ℕ) :
    terminalDistance family address depth ≤ upper ^ depth := by
  induction depth with
  | zero => simp
  | succ depth inductionHypothesis =>
      calc
        terminalDistance family address (depth + 1) ≤
            upper * terminalDistance family address depth :=
          terminalDistance_succ_le_upper_mul family nonnegative cardUpper address depth
        _ ≤ upper * upper ^ depth :=
          mul_le_mul_of_nonneg_left inductionHypothesis nonnegative
        _ = upper ^ (depth + 1) := by rw [pow_succ]; ring

/-- Both depth bounds, assuming only nonnegativity of the lower length bound;
nonnegativity of the upper bound follows from the nonempty path family. -/
theorem terminalDistance_bounds
    (family : List Edge → PathFamily Edge) {lower upper : ℝ}
    (lowerNonnegative : 0 ≤ lower)
    (cardBounds : ∀ address path, path ∈ (family address).paths →
      lower ≤ (path.card : ℝ) ∧ (path.card : ℝ) ≤ upper)
    (address : List Edge) (depth : ℕ) :
    lower ^ depth ≤ terminalDistance family address depth ∧
      terminalDistance family address depth ≤ upper ^ depth := by
  have upperNonnegative : 0 ≤ upper := by
    obtain ⟨path, membership⟩ := (family address).nonempty
    exact lowerNonnegative.trans
      ((cardBounds address path membership).1.trans (cardBounds address path membership).2)
  exact ⟨lower_pow_le_terminalDistance family lowerNonnegative
      (fun address path membership => (cardBounds address path membership).1) address depth,
    terminalDistance_le_upper_pow family upperNonnegative
      (fun address path membership => (cardBounds address path membership).2) address depth⟩

/-- Equal path cardinality at every address forces an exact deterministic
terminal distance, including the possible zero-length case. -/
theorem terminalDistance_eq_pow_of_equal_path_card
    (family : List Edge → PathFamily Edge) (length : ℝ)
    (equalCard : ∀ address path, path ∈ (family address).paths → (path.card : ℝ) = length)
    (address : List Edge) (depth : ℕ) :
    terminalDistance family address depth = length ^ depth := by
  have nonnegative : 0 ≤ length := by
    obtain ⟨path, membership⟩ := (family address).nonempty
    rw [← equalCard address path membership]
    positivity
  apply le_antisymm
  · exact terminalDistance_le_upper_pow family nonnegative
      (fun address path membership => le_of_eq (equalCard address path membership)) address depth
  · exact lower_pow_le_terminalDistance family nonnegative
      (fun address path membership => le_of_eq (equalCard address path membership).symm) address depth

end IGSIII.Chemical
