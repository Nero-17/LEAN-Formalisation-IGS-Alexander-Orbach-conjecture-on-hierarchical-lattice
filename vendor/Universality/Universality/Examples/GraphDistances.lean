import Universality.Graph.SubstitutionDistance
import Universality.Examples.GraphNoncommutativity

namespace Universality
noncomputable section
open FiniteNetwork

def wheatstoneDistanceCertificate : wheatstoneNetwork.DistanceCertificate where
  length := 2
  height := ![0, 2, 1, 1]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := .cons (by decide : wheatstoneNetwork.fullGraph.Adj 0 2)
    (.cons (by decide : wheatstoneNetwork.fullGraph.Adj 2 1) .nil)
  walk_length := rfl

def oppositeWheatstoneDistanceCertificate : oppositeWheatstoneNetwork.DistanceCertificate where
  length := 3
  height := ![0, 3, 2, 1, 1, 1, 2, 2]
  source_height := rfl
  target_height := rfl
  edge_bound := by decide
  walk := .cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 0 3)
    (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 3 6)
      (.cons (by decide : oppositeWheatstoneNetwork.fullGraph.Adj 6 1) .nil))
  walk_length := rfl

def Rule.multiplyDistanceCertificates (outer inner : Rule)
    (first : outer.network.DistanceCertificate) (second : inner.network.DistanceCertificate) :
    (outer * inner).network.DistanceCertificate :=
  first.substitute outer.network inner.network second

def groupedDistanceCertificate : groupedRule.network.DistanceCertificate :=
  Rule.multiplyDistanceCertificates
    ((wheatstoneRule * wheatstoneRule) * oppositeWheatstoneRule) oppositeWheatstoneRule
    (Rule.multiplyDistanceCertificates (wheatstoneRule * wheatstoneRule) oppositeWheatstoneRule
      (Rule.multiplyDistanceCertificates wheatstoneRule wheatstoneRule
        wheatstoneDistanceCertificate wheatstoneDistanceCertificate)
      oppositeWheatstoneDistanceCertificate)
    oppositeWheatstoneDistanceCertificate

def alternatingDistanceCertificate : alternatingRule.network.DistanceCertificate :=
  Rule.multiplyDistanceCertificates
    ((wheatstoneRule * oppositeWheatstoneRule) * wheatstoneRule) oppositeWheatstoneRule
    (Rule.multiplyDistanceCertificates (wheatstoneRule * oppositeWheatstoneRule) wheatstoneRule
      (Rule.multiplyDistanceCertificates wheatstoneRule oppositeWheatstoneRule
        wheatstoneDistanceCertificate oppositeWheatstoneDistanceCertificate)
      wheatstoneDistanceCertificate)
    oppositeWheatstoneDistanceCertificate

theorem wheatstone_terminal_distance :
    wheatstoneNetwork.fullGraph.dist wheatstoneNetwork.source wheatstoneNetwork.target = 2 :=
  wheatstoneDistanceCertificate.distance_eq _

theorem oppositeWheatstone_terminal_distance :
    oppositeWheatstoneNetwork.fullGraph.dist oppositeWheatstoneNetwork.source oppositeWheatstoneNetwork.target = 3 :=
  oppositeWheatstoneDistanceCertificate.distance_eq _

theorem reordered_rules_terminal_distances :
    groupedRule.network.fullGraph.dist groupedRule.network.source groupedRule.network.target = 36 ∧
      alternatingRule.network.fullGraph.dist alternatingRule.network.source alternatingRule.network.target = 36 :=
  ⟨groupedDistanceCertificate.distance_eq _, alternatingDistanceCertificate.distance_eq _⟩

end
end Universality
