import Universality.Geometry.PercolationGraphDirectedLimit

namespace Universality.Rule
noncomputable section
open FiniteNetwork

/-- A node stores its actual cell configurations and its two inherited terminal flags. -/
structure PercolationCellProcess (rule : Rule) where
  configuration : ∀ n, Configuration (rule.generation n).edges
  sourceSelected : Bool
  targetSelected : Bool

namespace PercolationCellProcess
variable {rule : Rule}

def Coherent (process : PercolationCellProcess rule) : Prop :=
  ∀ n, rule.coarsenGeneration n (process.configuration (n + 1)) = process.configuration n

def child (process : PercolationCellProcess rule) (edge : Fin rule.edges) : PercolationCellProcess rule where
  configuration n := rule.percolationCellConfiguration n (process.configuration (n + 1)) edge
  sourceSelected := (rule.network.orientedChildState process.sourceSelected process.targetSelected
    (process.configuration 0) edge).sourceSelected
  targetSelected := (rule.network.orientedChildState process.sourceSelected process.targetSelected
    (process.configuration 0) edge).targetSelected

theorem child_coherent (process : PercolationCellProcess rule) (h : process.Coherent)
    (edge : Fin rule.edges) : (process.child edge).Coherent :=
  rule.percolationCellConfiguration_coherent process.configuration h edge

def atAddress (process : PercolationCellProcess rule) : List (Fin rule.edges) → PercolationCellProcess rule
  | [] => process
  | edge :: address => (process.child edge).atAddress address

theorem atAddress_coherent (process : PercolationCellProcess rule) (h : process.Coherent)
    (address : List (Fin rule.edges)) : (process.atAddress address).Coherent := by
  induction address generalizing process with
  | nil => exact h
  | cons edge address ih => exact ih (process.child edge) (process.child_coherent h edge)

def limit (process : PercolationCellProcess rule) (h : rule.Classical) : Set (GenerationMetricSpace h) :=
  percolationSelectedLimit h process.configuration process.sourceSelected process.targetSelected

theorem limit_compact (process : PercolationCellProcess rule) (h : rule.Classical) :
    IsCompact (process.limit h) := isClosed_closure.isCompact

/-- The same finite-type recursive equation holds at every actual ancestral address. -/
theorem graphDirected_at_every_address (process : PercolationCellProcess rule) (h : rule.Classical)
    (hcoherent : process.Coherent) (address : List (Fin rule.edges)) :
    (process.atAddress address).limit h = ⋃ edge : Fin rule.edges,
      generationMetricCell h edge '' ((process.atAddress address).child edge).limit h :=
  percolationSelectedLimit_graphDirected h _ (process.atAddress_coherent hcoherent address) _ _

theorem child_state_at_every_depth (process : PercolationCellProcess rule)
    (hcoherent : process.Coherent) (address : List (Fin rule.edges)) (depth : ℕ) (edge : Fin rule.edges) :
    rule.percolationCellState depth ((process.atAddress address).configuration (depth + 1))
      (process.atAddress address).sourceSelected (process.atAddress address).targetSelected edge =
    rule.network.orientedChildState (process.atAddress address).sourceSelected
      (process.atAddress address).targetSelected ((process.atAddress address).configuration 0) edge :=
  rule.percolationCellState_eq _ (process.atAddress_coherent hcoherent address) depth _ _ edge

end PercolationCellProcess
end
end Universality.Rule
