module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStackProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackSlotsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalFinitePrefixAppendProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseStackSlotsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationStepPeelSupportProof (andIntro)
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalResultStackSlotsSupportProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem dropChild (count front backwardRow produced old childOld results : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph count front)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front backwardRow)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append childOld backwardRow old)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old))) :
    Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.drop childOld count results)) := by
  have hj := SixSol20261112.Runtime.AppendReassociationProof.appendReassociation body alpha Delta front backwardRow old produced childOld results hp hc hr
  obtain ⟨hf⟩ := OriginalResultStackPartitionProof.actualPartition body alpha Delta count front childOld results hl hj
  exact ⟨Derivation.conjunctionRight hf⟩

theorem oneAt (count front backwardRow produced old childOld results first : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph count front)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front backwardRow)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append childOld backwardRow old)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardRow first z))) :
    Nonempty (Derivation body Delta
      (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc z) count results ⊓
       graph3 OriginalHereditaryResultStackProgram.secondSlot z (suc z) count results)) := by
  have hd := dropChild count front backwardRow produced old childOld results hl hp hc hr
  have hrow := OriginalHereditaryInternalFinitePrefixAppendProof.unaryAppended backwardRow first old childOld hb hc
  have hv := InternalRawListRecursionSupportProof.lookupValue first count results childOld hd
    (InternalRawListRecursionSupportProof.consHead childOld first old hrow)
  exact InternalApplicationStepPeelSupportProof.andIntro
    (firstAt z count results (suc count) count first (additionOne count)
      (InternalEqualityTestPredecessorProof.predecessorSuccessor count) hv) (secondOne count results)

theorem twoAt (count front backwardRow backwardTail produced old childOld tailOld results first second : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph count front)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front backwardRow)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append childOld backwardRow old)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardRow second backwardTail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardTail first z)))
    (ho : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tailOld first old))) :
    Nonempty (Derivation body Delta
      (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc (suc z)) count results ⊓
       graph3 OriginalHereditaryResultStackProgram.secondSlot second (suc (suc z)) count results)) := by
  have hd := dropChild count front backwardRow produced old childOld results hl hp hc hr
  have hrow := OriginalHereditaryInternalFinitePrefixAppendProof.binaryAppended backwardRow second backwardTail first old tailOld childOld hb ht ho hc
  have hs := InternalRawListRecursionSupportProof.lookupValue second count results childOld hd
    (InternalRawListRecursionSupportProof.consHead childOld second tailOld hrow)
  have hdt := InternalRawListRecursionSupportProof.dropNext tailOld childOld count results hd
    (InternalRawListRecursionSupportProof.consTail childOld second tailOld hrow)
  have hf := InternalRawListRecursionSupportProof.lookupValue first (suc count) results tailOld hdt
    (InternalRawListRecursionSupportProof.consHead tailOld first old ho)
  exact InternalApplicationStepPeelSupportProof.andIntro
    (firstAt (suc z) count results (suc (suc count)) (suc count) first (additionTwo count)
      (InternalEqualityTestPredecessorProof.predecessorSuccessor (suc count)) hf) (secondTwo count results second hs)

theorem one (count front backwardRow produced old results first : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph count front)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front backwardRow)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardRow first z)))
    : Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc z) count results ⊓ graph3 OriginalHereditaryResultStackProgram.secondSlot z (suc z) count results)) := by
  apply programCases InternalApplicationValidityStackAppend.append (Fin.cons backwardRow (Fin.cons old Fin.elim0)) _
  intro beta j Theta childOld hj hc
  simp only [consTermRename,emptyRename] at hc
  simp only [conjunctionRename,graph3Rename,zRelabel,sucRelabel]
  have hl' := renameInto hl j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have hb' := renameInto hb j Theta hj
  simp only [lengthRename,graph2Rename,zRelabel] at hl' hp' hr' hb'
  exact oneAt (count.relabel j) (front.relabel j) (backwardRow.relabel j) (produced.relabel j) (old.relabel j) childOld (results.relabel j) (first.relabel j) hl' hp' hc hr' hb'

theorem two (count front backwardRow backwardTail produced old results first second : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph count front)))
    (hp : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced front backwardRow)))
    (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append results produced old)))
    (hb : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardRow second backwardTail)))
    (ht : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode backwardTail first z)))
    : Nonempty (Derivation body Delta (graph3 OriginalHereditaryResultStackProgram.firstSlot first (suc (suc z)) count results ⊓ graph3 OriginalHereditaryResultStackProgram.secondSlot second (suc (suc z)) count results)) := by
  let qs : Fin 2 → LogicLineages.ComputabilityKnowledge.GorbowPRProgram.Program 3 :=
    ![.composition InternalApplicationValidityStackAppend.append ![.projection 0,.projection 1],
      .composition InternalListCodec.consCode ![.projection 2,.projection 1]]
  let xs : Fin 3 → OTerm alpha := ![backwardRow,old,first]
  apply queryCases qs xs _
  intro beta j ys Theta hj hq
  let xx : Fin 3 → OTerm beta := ![backwardRow.relabel j,old.relabel j,first.relabel j]
  have hx : (fun i => (xs i).relabel j) = xx := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro i
      refine Fin.cases ?_ ?_ i
      · rfl
      · intro i
        refine Fin.cases ?_ (fun k => Fin.elim0 k) i
        rfl
  rw [hx] at hq
  have hc := binaryRecover InternalApplicationValidityStackAppend.append (.projection 0) (.projection 1)
    (ys 0) (backwardRow.relabel j) (old.relabel j) xx (hq 0) (projectionValue 0 xx) (projectionValue 1 xx)
  have ho := binaryRecover InternalListCodec.consCode (.projection 2) (.projection 1)
    (ys 1) (first.relabel j) (old.relabel j) xx (hq 1) (projectionValue 2 xx) (projectionValue 1 xx)
  simp only [conjunctionRename,graph3Rename,zRelabel,sucRelabel]
  have hl' := renameInto hl j Theta hj
  have hp' := renameInto hp j Theta hj
  have hr' := renameInto hr j Theta hj
  have hb' := renameInto hb j Theta hj
  have ht' := renameInto ht j Theta hj
  simp only [lengthRename,graph2Rename,zRelabel] at hl' hp' hr' hb' ht'
  exact twoAt (count.relabel j) (front.relabel j) (backwardRow.relabel j) (backwardTail.relabel j) (produced.relabel j) (old.relabel j) (ys 0) (ys 1) (results.relabel j) (first.relabel j) (second.relabel j) hl' hp' hc hr' hb' ht' ho
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseStackSlotsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ReverseStackSlotsProof
