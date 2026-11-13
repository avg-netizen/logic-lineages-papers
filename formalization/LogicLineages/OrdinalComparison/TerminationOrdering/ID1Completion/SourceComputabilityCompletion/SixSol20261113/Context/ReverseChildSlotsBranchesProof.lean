module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseForwardRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseActualRowsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseStackSlotsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackZeroSlotsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsBranchesProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open InternalTagArithmeticSupportProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zero (deletionCount forwardRow backwardRow deletionPrefix produced old results first second : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph z forwardRow)))
    (hrev : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardRow forwardRow)))
    (hd : Nonempty (Derivation body Delta (lengthGraph deletionCount deletionPrefix)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backwardRow)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z forwardRow)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) forwardRow)))
    : Nonempty (Derivation body Delta
      (graph3 OriginalHereditaryResultStackProgram.firstSlot first z deletionCount results ⊓
       graph3 OriginalHereditaryResultStackProgram.secondSlot second z deletionCount results)) := by
  have he := OriginalContextInsertionLengthProof.lengthZeroRecover forwardRow hl
  have hf0 := AdmittedLengthCasesProof.binaryInputs InternalRawListRecursion.lookup first z forwardRow z z ⟨refl z⟩ he hf
  have hs0 := AdmittedLengthCasesProof.binaryInputs InternalRawListRecursion.lookup second (suc z) forwardRow (suc z) z ⟨refl (suc z)⟩ he hs
  obtain ⟨ef⟩ := valueUnique InternalRawListRecursion.lookup first z (Fin.cons z (Fin.cons z Fin.elim0)) hf0 ReverseForwardRowsProof.lookupNilZero
  obtain ⟨es⟩ := valueUnique InternalRawListRecursion.lookup second z (Fin.cons (suc z) (Fin.cons z Fin.elim0)) hs0 ReverseForwardRowsProof.lookupNilOne
  have hz := OriginalResultStackZeroSlotsProof.actualZero body alpha Delta deletionCount results
  exact InternalApplicationStepPeelSupportProof.andIntro
    (outputTransport OriginalHereditaryResultStackProgram.firstSlot z first (Fin.cons z (Fin.cons deletionCount (Fin.cons results Fin.elim0))) ⟨symm ef⟩ (InternalApplicationStepPeelSupportProof.andLeft hz))
    (outputTransport OriginalHereditaryResultStackProgram.secondSlot z second (Fin.cons z (Fin.cons deletionCount (Fin.cons results Fin.elim0))) ⟨symm es⟩ (InternalApplicationStepPeelSupportProof.andRight hz))

theorem one (deletionCount forwardRow backwardRow deletionPrefix produced old results first second : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc z) forwardRow)))
    (hrev : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardRow forwardRow)))
    (hd : Nonempty (Derivation body Delta (lengthGraph deletionCount deletionPrefix)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backwardRow)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z forwardRow)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) forwardRow)))
    : Nonempty (Derivation body Delta
      (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc z) deletionCount results ⊓
       graph3 OriginalHereditaryResultStackProgram.secondSlot second (suc z) deletionCount results)) := by
  have hforward := ReverseForwardRowsProof.singleton forwardRow first hl hf
  obtain ⟨es⟩ := ReverseForwardRowsProof.secondDefault forwardRow first second hforward hs
  have hback := ReverseActualRowsProof.singleton forwardRow backwardRow first hforward hrev
  have hv := ReverseStackSlotsProof.one deletionCount deletionPrefix backwardRow produced old results first hd hp hr hback
  exact InternalApplicationStepPeelSupportProof.andIntro (InternalApplicationStepPeelSupportProof.andLeft hv)
    (outputTransport OriginalHereditaryResultStackProgram.secondSlot z second
      (Fin.cons (suc z) (Fin.cons deletionCount (Fin.cons results Fin.elim0))) ⟨symm es⟩ (InternalApplicationStepPeelSupportProof.andRight hv))

theorem two (deletionCount forwardRow backwardRow deletionPrefix produced old results first second : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph (suc (suc z)) forwardRow)))
    (hrev : Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse backwardRow forwardRow)))
    (hd : Nonempty (Derivation body Delta (lengthGraph deletionCount deletionPrefix)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced deletionPrefix backwardRow)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hf : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup first z forwardRow)))
    (hs : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup second (suc z) forwardRow)))
    : Nonempty (Derivation body Delta
      (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc (suc z)) deletionCount results ⊓
       graph3 OriginalHereditaryResultStackProgram.secondSlot second (suc (suc z)) deletionCount results)) := by
  apply ReverseForwardRowsProof.binaryCases forwardRow first second _ hl hf hs
  intro beta j Theta tail hj hforward htail
  apply programCases InternalListCodec.consCode (Fin.cons (first.relabel j) (Fin.cons z Fin.elim0)) _
  intro gamma k Xi singletonFirst hk hsingle
  simp only [consTermRename,emptyRename,zRelabel] at hsingle
  simp only [conjunctionRename,graph3Rename,zRelabel,sucRelabel]
  have hforward' := renameInto hforward k Xi hk
  have htail' := renameInto htail k Xi hk
  have hrev' := renameInto (renameInto hrev j Theta hj) k Xi hk
  have hd' := renameInto (renameInto hd j Theta hj) k Xi hk
  have hp' := renameInto (renameInto hp j Theta hj) k Xi hk
  have hr' := renameInto (renameInto hr j Theta hj) k Xi hk
  simp only [graph1Rename,graph2Rename,lengthRename,zRelabel] at hforward' htail' hrev' hd' hp' hr'
  have hback := ReverseActualRowsProof.binaryAtSingleton ((forwardRow.relabel j).relabel k) ((backwardRow.relabel j).relabel k)
    ((first.relabel j).relabel k) ((second.relabel j).relabel k) (tail.relabel k) singletonFirst hforward' htail' hsingle hrev'
  exact ReverseStackSlotsProof.two ((deletionCount.relabel j).relabel k) ((deletionPrefix.relabel j).relabel k)
    ((backwardRow.relabel j).relabel k) singletonFirst ((produced.relabel j).relabel k) ((old.relabel j).relabel k)
    ((results.relabel j).relabel k) ((first.relabel j).relabel k) ((second.relabel j).relabel k) hd' hp' hr' hback hsingle
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsBranchesProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseChildSlotsBranchesProof
