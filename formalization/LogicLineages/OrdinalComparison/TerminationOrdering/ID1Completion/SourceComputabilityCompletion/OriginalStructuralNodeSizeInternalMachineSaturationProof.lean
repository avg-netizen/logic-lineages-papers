module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineTerminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalAlgebraProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineSaturationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalRawSyntaxTransport OriginalRawSyntaxTransportInternalMachineState
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open InternalTagArithmeticSupportProof (trans)
open OriginalStructuralNodeSizeInternalMachineCompletion OriginalStructuralNodeSizeInternalMachineCompletionSyntaxProof
open OriginalStructuralNodeSizeInternalMachineCompletionBindingProof OriginalStructuralNodeSizeInternalMachineCompletionInductionProof
open OriginalStructuralNodeSizeInternalMachineTerminationProof
open OriginalHereditaryValidityInternalRecurrenceIterationBoundSyntaxProof (weakBoundRename)
open InternalApplicationCertifiedResultFoldClosureBridgeStateProof (payloadFuelRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {positive : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem agreeAtCompletion
    (d k raw count produced budgetA budgetB start stateA stateB : OTerm alpha)
    (hb : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound count (payloadFuel raw))))
    (hbA : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (payloadFuel raw) budgetA)))
    (hbB : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (payloadFuel raw) budgetB)))
    (hc : Nonempty (Derivation positive Delta (Completes d k raw count produced)))
    (hi : Nonempty (Derivation positive Delta (graph3 initial start d k raw)))
    (hrA : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) stateA budgetA start)))
    (hrB : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) stateB budgetB start))) :
    Nonempty (Derivation positive Delta (equal stateA stateB)) := by
  apply programCases finishedState (Fin.cons produced Fin.elim0) _
  intro beta j Theta finish hj hf
  rw [equalEqn,eqnRelabel]
  have hb' := renameInto hb j Theta hj
  have hbA' := renameInto hbA j Theta hj
  have hbB' := renameInto hbB j Theta hj
  have hc' := renameInto hc j Theta hj
  have hi' := renameInto hi j Theta hj
  have hrA' := renameInto hrA j Theta hj
  have hrB' := renameInto hrB j Theta hj
  simp only [weakBoundRename,payloadFuelRename] at hb' hbA' hbB'
  rw [completesRename] at hc'
  rw [graph3Rename] at hi'
  rw [graph2Rename] at hrA' hrB'
  simp only [consTermRename,emptyRename] at hf
  have ha := iterateAtStates (d.relabel j) (k.relabel j) (raw.relabel j) (count.relabel j)
    (budgetA.relabel j) (produced.relabel j) (start.relabel j) finish hb' hbA' hc' hi' hf
  have hb := iterateAtStates (d.relabel j) (k.relabel j) (raw.relabel j) (count.relabel j)
    (budgetB.relabel j) (produced.relabel j) (start.relabel j) finish hb' hbB' hc' hi' hf
  obtain ⟨heA⟩ := valueUnique (OriginalStructuralNodeSize.iterate) (stateA.relabel j) finish ![budgetA.relabel j,start.relabel j] hrA' ha
  obtain ⟨heB⟩ := valueUnique (OriginalStructuralNodeSize.iterate) finish (stateB.relabel j) ![budgetB.relabel j,start.relabel j] hb hrB'
  exact ⟨trans heA heB⟩

/-- Two-way saturation at any two sufficient budgets. The actual encoded
states agree, not merely a decoded result or an externally calibrated value. -/
theorem saturation (d k raw budgetA budgetB start stateA stateB : OTerm alpha)
    (hbA : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (payloadFuel raw) budgetA)))
    (hbB : Nonempty (Derivation positive Delta (InternalPairingSumBounds.weakBound (payloadFuel raw) budgetB)))
    (hi : Nonempty (Derivation positive Delta (graph3 initial start d k raw)))
    (hrA : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) stateA budgetA start)))
    (hrB : Nonempty (Derivation positive Delta (graph2 (OriginalStructuralNodeSize.iterate) stateB budgetB start))) :
    Nonempty (Derivation positive Delta (equal stateA stateB)) := by
  apply hasCompletionCases d k raw raw _ (hasCompletion d k raw)
  intro beta j Theta count produced hj hb hc
  rw [equalEqn,eqnRelabel]
  have hbA' := renameInto hbA j Theta hj
  have hbB' := renameInto hbB j Theta hj
  have hi' := renameInto hi j Theta hj
  have hrA' := renameInto hrA j Theta hj
  have hrB' := renameInto hrB j Theta hj
  simp only [weakBoundRename,payloadFuelRename] at hbA' hbB'
  rw [graph3Rename] at hi'
  rw [graph2Rename] at hrA' hrB'
  simpa only [equalEqn] using agreeAtCompletion (d.relabel j) (k.relabel j) (raw.relabel j) count produced
    (budgetA.relabel j) (budgetB.relabel j) (start.relabel j) (stateA.relabel j) (stateB.relabel j)
    hb hbA' hbB' hc hi' hrA' hrB'

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineSaturationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalStructuralNodeSizeInternalMachineSaturationProof
