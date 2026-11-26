module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel zRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open VisitListCompletionDefinitions VisitListCompletionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withProduced (R : Program 2)
 (size job frame tailTagged tagged headCount value tailCount tailRow singleFrame singleValue : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size tailRow ⊓ PrefixFrameDefinitions.PrefixFrame R tailTagged tailCount tailRow)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleFrame frame z)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleValue value z)))
 : Nonempty (Derivation body Delta (Completion R (suc size) tagged)) := by
 apply programCases InternalApplicationValidityStackAppend.append (Fin.cons tailRow (Fin.cons singleValue Fin.elim0)) _
 intro beta j Theta produced hinc hq
 simp only [completionRename,sucRelabel]
 simp only [consTermRename,emptyRename,zRelabel] at hq
 have hh' := renameInto hh j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hp' := renameInto hp j Theta hinc
 have hv' := renameInto hv j Theta hinc
 simp only [JobFrameSyntax.frameRename,PrefixFrameSyntax.frameRename,InternalRecursionGraphStepSyntaxProof.conjunctionRename,OriginalContextInsertionSyntaxProof.lengthRename,graph2Rename,zRelabel] at hh' ht' hf' hc' hp' hv'
 exact VisitListCompletionConsCore.consCore R (size.relabel j) (job.relabel j) (frame.relabel j) (tailTagged.relabel j) (tagged.relabel j) (headCount.relabel j) (value.relabel j) (tailCount.relabel j) (tailRow.relabel j) (singleFrame.relabel j) (singleValue.relabel j) produced
   hh' ht' hf' hc' hp' hv' hq
theorem withSingleValue (R : Program 2)
 (size job frame tailTagged tagged headCount value tailCount tailRow singleFrame : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size tailRow ⊓ PrefixFrameDefinitions.PrefixFrame R tailTagged tailCount tailRow)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleFrame frame z)))
 : Nonempty (Derivation body Delta (Completion R (suc size) tagged)) := by
 apply programCases InternalListCodec.consCode (Fin.cons value (Fin.cons z Fin.elim0)) _
 intro beta j Theta singleValue hinc hq
 simp only [completionRename,sucRelabel]
 simp only [consTermRename,emptyRename,zRelabel] at hq
 have hh' := renameInto hh j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 have hp' := renameInto hp j Theta hinc
 simp only [JobFrameSyntax.frameRename,PrefixFrameSyntax.frameRename,InternalRecursionGraphStepSyntaxProof.conjunctionRename,OriginalContextInsertionSyntaxProof.lengthRename,graph2Rename,zRelabel] at hh' ht' hf' hc' hp'
 exact withProduced R (size.relabel j) (job.relabel j) (frame.relabel j) (tailTagged.relabel j) (tagged.relabel j) (headCount.relabel j) (value.relabel j) (tailCount.relabel j) (tailRow.relabel j) (singleFrame.relabel j) singleValue
   hh' ht' hf' hc' hp' hq
theorem withSingleFrame (R : Program 2)
 (size job frame tailTagged tagged headCount value tailCount tailRow : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size tailRow ⊓ PrefixFrameDefinitions.PrefixFrame R tailTagged tailCount tailRow)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)))
 : Nonempty (Derivation body Delta (Completion R (suc size) tagged)) := by
 apply programCases InternalListCodec.consCode (Fin.cons frame (Fin.cons z Fin.elim0)) _
 intro beta j Theta singleFrame hinc hq
 simp only [completionRename,sucRelabel]
 simp only [consTermRename,emptyRename,zRelabel] at hq
 have hh' := renameInto hh j Theta hinc
 have ht' := renameInto ht j Theta hinc
 have hf' := renameInto hf j Theta hinc
 have hc' := renameInto hc j Theta hinc
 simp only [JobFrameSyntax.frameRename,PrefixFrameSyntax.frameRename,InternalRecursionGraphStepSyntaxProof.conjunctionRename,OriginalContextInsertionSyntaxProof.lengthRename,graph2Rename,zRelabel] at hh' ht' hf' hc'
 exact withSingleValue R (size.relabel j) (job.relabel j) (frame.relabel j) (tailTagged.relabel j) (tagged.relabel j) (headCount.relabel j) (value.relabel j) (tailCount.relabel j) (tailRow.relabel j) singleFrame
   hh' ht' hf' hc' hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsQueries
