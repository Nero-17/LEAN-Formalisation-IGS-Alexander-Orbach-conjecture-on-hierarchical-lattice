import IGSIII4.SpectralDensity.ActualMomentCircuitFlow

set_option autoImplicit false
set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false

namespace IGSIII4.SpectralDensity.ActualFamily
noncomputable section
open scoped BigOperators
open IGSIII34.Resistance
attribute [local instance] Classical.propDecidable

variable {blocks paths interior : ℕ}

def shortEdge (edge : Fin 2) : Edge blocks paths interior :=
  .inl ⟨edge.val, by omega⟩

def circuitPotential (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (voltage shortCurrent : ℝ)
    (junctionPotential : Fin (blocks + 1) → ℝ)
    (pathCurrent : Fin blocks → Fin paths → ℝ) : Vertex blocks paths interior → ℝ
  | .inl vertex => if vertex.val = 0 then voltage
      else if vertex.val = 1 then
        openPathPotential (fun edge => configuration (shortEdge edge))
          (fun edge => resistance (shortEdge edge)) shortCurrent voltage 0 1
      else 0
  | .inr (.inl junction) => junctionPotential junction
  | .inr (.inr (block, path, position)) =>
      openPathPotential (fun edge => configuration (.inr (block, path, edge)))
        (fun edge => resistance (.inr (block, path, edge))) (pathCurrent block path)
        (junctionPotential block.castSucc) (junctionPotential block.succ) position.succ.castSucc

theorem circuitPotential_pathVertex
    (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (voltage shortCurrent : ℝ)
    (junctionPotential : Fin (blocks + 1) → ℝ)
    (pathCurrent : Fin blocks → Fin paths → ℝ)
    (pathVoltage : ∀ block path, (∀ edge : Fin (interior + 2),
      configuration (.inr (block, path, edge)) = true) →
      pathCurrent block path * (∑ edge : Fin (interior + 2), resistance (.inr (block, path, edge))) =
        junctionPotential block.castSucc - junctionPotential block.succ)
    (block : Fin blocks) (path : Fin paths) (position : Fin (interior + 3)) :
    circuitPotential configuration resistance voltage shortCurrent junctionPotential pathCurrent
      (pathVertex blocks paths interior block path position) =
      openPathPotential (fun edge => configuration (.inr (block, path, edge)))
        (fun edge => resistance (.inr (block, path, edge))) (pathCurrent block path)
        (junctionPotential block.castSucc) (junctionPotential block.succ) position := by
  unfold pathVertex
  split_ifs with first last
  · have equal : position = 0 := Fin.ext first
    subst position
    simpa only [circuitPotential] using
      (openPathPotential_left (fun edge => configuration (.inr (block, path, edge)))
        (fun edge => resistance (.inr (block, path, edge))) (pathCurrent block path)
        (junctionPotential block.castSucc) (junctionPotential block.succ)).symm
  · have equal : position = Fin.last (interior + 2) := Fin.ext last
    subst position
    simpa only [circuitPotential] using
      (openPathPotential_right (fun edge => configuration (.inr (block, path, edge)))
        (fun edge => resistance (.inr (block, path, edge))) (pathCurrent block path)
        (junctionPotential block.castSucc) (junctionPotential block.succ) (pathVoltage block path)).symm
  · simp only [circuitPotential]
    congr 1
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_succ]
    omega

/-- Explicit currents and path potentials identify the weighted response of
the actual typed open graph, including every failed path fragment. Local
voltage identities are the algebraic interface to the circuit formula. -/
theorem actual_circuit_voltage_of_local_identities
    (configuration : Edge blocks paths interior → Bool)
    (resistance : Edge blocks paths interior → ℝ) (positive : ∀ edge, 0 < resistance edge)
    (voltage shortCurrent exteriorCurrent : ℝ)
    (junctionPotential : Fin (blocks + 1) → ℝ)
    (pathCurrent : Fin blocks → Fin paths → ℝ)
    (blockBalance : ∀ block, ∑ path, pathCurrent block path = exteriorCurrent)
    (total : shortCurrent + exteriorCurrent = 1)
    (closedZero : ∀ edge, configuration edge ≠ true →
      circuitCurrent blocks paths interior shortCurrent exteriorCurrent pathCurrent edge = 0)
    (shortVoltage : (∀ edge : Fin 2, configuration (shortEdge edge) = true) →
      shortCurrent * (∑ edge : Fin 2, resistance (shortEdge edge)) = voltage)
    (shortZero : (¬∀ edge : Fin 2, configuration (shortEdge edge) = true) → shortCurrent = 0)
    (pathVoltage : ∀ block path, (∀ edge : Fin (interior + 2),
      configuration (.inr (block, path, edge)) = true) →
      pathCurrent block path * (∑ edge : Fin (interior + 2), resistance (.inr (block, path, edge))) =
        junctionPotential block.castSucc - junctionPotential block.succ)
    (pathZero : ∀ block path, (¬∀ edge : Fin (interior + 2),
      configuration (.inr (block, path, edge)) = true) → pathCurrent block path = 0)
    (leftExterior : configuration (.inl 2) = true →
      resistance (.inl 2) * exteriorCurrent = voltage - junctionPotential 0)
    (rightExterior : configuration (.inl 3) = true →
      resistance (.inl 3) * exteriorCurrent = junctionPotential (Fin.last blocks)) :
    (openElectricalNetwork blocks paths interior configuration).effectiveResistance
      (fun edge => resistance edge.val) = voltage := by
  let current := circuitCurrent blocks paths interior shortCurrent exteriorCurrent pathCurrent
  let potential := circuitPotential configuration resistance voltage shortCurrent junctionPotential pathCurrent
  have fullFlow := circuitCurrent_unit_flow (interior := interior)
    shortCurrent exteriorCurrent pathCurrent blockBalance total
  have supported : ∀ edge ∉ Set.range (Subtype.val :
      {edge : Edge blocks paths interior // configuration edge = true} → Edge blocks paths interior),
      current edge = 0 := by
    intro edge outside
    apply closedZero edge
    intro opened
    exact outside ⟨⟨edge, opened⟩, rfl⟩
  have openFlow : (fun edge : {edge : Edge blocks paths interior // configuration edge = true} =>
      current edge.val) ∈ (openElectricalNetwork blocks paths interior configuration).unitFlows := by
    intro vertex
    rw [IGSIII34.Resistance.FiniteNetwork.supported_current_divergence_restriction_completion
      (fullElectricalNetwork blocks paths interior)
      (openElectricalNetwork blocks paths interior configuration) Subtype.val Subtype.val_injective
      (fun _ => rfl) current supported]
    exact fullFlow vertex
  have shortRight : openPathPotential (fun edge => configuration (shortEdge edge))
      (fun edge => resistance (shortEdge edge)) shortCurrent voltage 0 (Fin.last 2) = 0 :=
    openPathPotential_right _ _ _ _ _ (by simpa using shortVoltage)
  have ohm : ∀ edge : {edge : Edge blocks paths interior // configuration edge = true},
      resistance edge.val * current edge.val =
        potential ((openElectricalNetwork blocks paths interior configuration).endpoint edge).1 -
        potential ((openElectricalNetwork blocks paths interior configuration).endpoint edge).2 := by
    rintro ⟨edge, opened⟩
    rcases edge with edge | ⟨block, path, edge⟩
    · fin_cases edge
      · have identity := openPathPotential_ohm
          (fun edge => configuration (shortEdge edge)) (fun edge => resistance (shortEdge edge))
          shortCurrent voltage 0 shortZero (0 : Fin 2) (by simpa [shortEdge] using opened)
        simpa [current, potential, circuitCurrent, circuitPotential, openElectricalNetwork,
          endpoint, source, midpoint, shortEdge, openPathPotential_left] using identity.symm
      · have identity := openPathPotential_ohm
          (fun edge => configuration (shortEdge edge)) (fun edge => resistance (shortEdge edge))
          shortCurrent voltage 0 shortZero (1 : Fin 2) (by simpa [shortEdge] using opened)
        rw [show (1 : Fin 2).succ = Fin.last 2 from rfl, shortRight, sub_zero] at identity
        simpa [current, potential, circuitCurrent, circuitPotential, openElectricalNetwork,
          endpoint, target, midpoint, shortEdge, shortRight] using identity.symm
      · simpa [current, potential, circuitCurrent, circuitPotential, openElectricalNetwork,
          endpoint, source] using leftExterior opened
      · simpa [current, potential, circuitCurrent, circuitPotential, openElectricalNetwork,
          endpoint, target] using rightExterior opened
    · have identity := openPathPotential_ohm
        (fun edge => configuration (.inr (block, path, edge)))
        (fun edge => resistance (.inr (block, path, edge))) (pathCurrent block path)
        (junctionPotential block.castSucc) (junctionPotential block.succ) (pathZero block path) edge opened
      change resistance (.inr (block, path, edge)) * pathCurrent block path =
        circuitPotential configuration resistance voltage shortCurrent junctionPotential pathCurrent
          (pathVertex blocks paths interior block path edge.castSucc) -
        circuitPotential configuration resistance voltage shortCurrent junctionPotential pathCurrent
          (pathVertex blocks paths interior block path edge.succ)
      rw [circuitPotential_pathVertex _ _ _ _ _ _ pathVoltage,
        circuitPotential_pathVertex _ _ _ _ _ _ pathVoltage]
      exact identity.symm
  have voltageIdentity := IGSIII34.Resistance.FiniteNetwork.effectiveResistance_eq_ohmic_voltage
    (openElectricalNetwork blocks paths interior configuration) (fun edge => resistance edge.val)
    (fun edge => current edge.val) potential (fun edge => (positive edge.val).le) openFlow ohm
  simpa [potential, circuitPotential, openElectricalNetwork, source, target] using voltageIdentity

end
end IGSIII4.SpectralDensity.ActualFamily
