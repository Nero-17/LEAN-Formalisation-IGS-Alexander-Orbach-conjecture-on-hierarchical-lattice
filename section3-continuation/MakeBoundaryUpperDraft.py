from pathlib import Path

source = Path('IGSIII34/Percolation/ElectricalBoundaryConditioning.lean').read_text(encoding='utf-8-sig')
source = source.replace('import IGSIII34.Percolation.ElectricalConditionalJensen', 'import ElectricalConditionalUpperDraft')
source = source[:source.index('theorem normalized_electrical_boundary_conditional_mean_lower')]
source = source.replace('theorem actual_electrical_boundary_conditional_mean_lower', 'theorem actual_electrical_boundary_conditional_mean_upper')
begin = source.index('    (inverseIntegrable :')
end = source.index('    (depth : ℕ)', begin)
source = source[:begin] + '''    (mean : ℝ) (meanNonnegative : 0 ≤ mean)
    (meanEquality : (∫ marks, value marks ∂independentInnovationLaw rule p positive belowOne fixedPoint) = mean)
''' + source[end:]
begin = source.index('      unitConfigurationResistance (rule.generation depth).network')
end = source.index(' := by', begin)
source = source[:begin] + '''      (independentInnovationLaw rule p positive belowOne fixedPoint)[fun marks =>
        electricalCell (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)
          (fun leaf => positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) |
        coordinatePrefixFiltration (fun coordinate : List (Fin rule.edges) × Bool => coordinate.1.length) (depth+1)] marks ≤
        mean * unitConfigurationResistance (rule.generation depth).network (markedGenerationConfiguration rule marks depth [] true)''' + source[end:]
begin = source.index('  have inverseEquality :')
end = source.index('  have boundaryMeasurable :', begin)
source = source[:begin] + source[end:]
begin = source.index('  have inverseInputIntegrable')
end = source.index('  have independent :=', begin)
source = source[:begin] + '''  have inputMean (leaf : Fin (rule.generation depth).edges) :
      (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        positiveRepresentative value (children leaf)
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) = mean := by
    have boundaryIntegral : (∫ children : Fin (rule.generation depth).edges → ((List (Fin rule.edges) × Bool) → Configuration rule.edges),
        positiveRepresentative value (children leaf)
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (fun marks (leaf : Fin (rule.generation depth).edges) => innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)) =
        ∫ marks, positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable boundaryMeasurable
        (representativeMeasurable.comp (measurable_pi_apply leaf)).stronglyMeasurable
    rw [boundaryIntegral]
    have shiftIntegral : (∫ marks, positiveRepresentative value marks
        ∂(independentInnovationLaw rule p positive belowOne fixedPoint).map
          (innovationTreeShift rule (generationEdgeAddress rule depth leaf))) =
        ∫ marks, positiveRepresentative value (innovationTreeShift rule (generationEdgeAddress rule depth leaf) marks)
          ∂independentInnovationLaw rule p positive belowOne fixedPoint :=
      integral_map_of_stronglyMeasurable
        (innovationTreeShift_measurable rule (generationEdgeAddress rule depth leaf)) representativeMeasurable.stronglyMeasurable
    rw [(innovationTreeShift_preserving rule p positive belowOne fixedPoint (generationEdgeAddress rule depth leaf)).map_eq] at shiftIntegral
    exact shiftIntegral.symm.trans ((integral_congr_ae representativeEquality).trans meanEquality)
''' + source[end:]
source = source.replace('independent_conditional_electrical_mean_lower', 'independent_conditional_electrical_mean_upper')
source = source.replace('inputIntegrable inverseInputIntegrable inverseMean inverseMeanPositive inverseInputMean',
                        'inputIntegrable mean meanNonnegative inputMean')
Path('ElectricalBoundaryUpperDraft.lean').write_text(source + '\nend\nend IGSIII34.Percolation\n', encoding='utf-8')
