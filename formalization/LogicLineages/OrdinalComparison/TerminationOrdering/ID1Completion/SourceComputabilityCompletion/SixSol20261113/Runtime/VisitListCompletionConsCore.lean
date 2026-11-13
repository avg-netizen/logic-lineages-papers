module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsCore
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalTagArithmeticSyntaxProof (z suc sucRelabel)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalAdditionLawsProof (add)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open VisitListCompletionDefinitions VisitListCompletionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualEmpty : VisitListCompletionTargets.ActualEmpty := by
 intro R body alpha Delta
 exact completionIntro R z z z z (andIntro OriginalContextInsertionLengthProof.lengthZero
   (PrefixFrameIdentityProof.actualIdentity R body alpha Delta))

theorem consCore (R : Program 2)
 (size job frame tailTagged tagged headCount value tailCount tailRow singleFrame singleValue produced : OTerm alpha)
 (hh : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job headCount value)))
 (ht : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size tailRow ⊓ PrefixFrameDefinitions.PrefixFrame R tailTagged tailCount tailRow)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame z job)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode tagged frame tailTagged)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleFrame frame z)))
 (hv : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode singleValue value z)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append produced tailRow singleValue))) :
 Nonempty (Derivation body Delta (Completion R (suc size) tagged)) := by
 have ha := InternalApplicationValidityStackAppendListProof.consBackward singleFrame frame z tailTagged tailTagged tagged
   hp (InternalApplicationValidityStackAppendListProof.appendZeroValue tailTagged) hc
 have hs := PrefixFrameSingletonProof.actualSingleton R body alpha Delta job headCount value frame singleFrame singleValue hh hf hp hv
 have hrun := PrefixFrameCompositionProof.actualConcatenation R body alpha Delta singleFrame tailTagged headCount tailCount
   singleValue tailRow tagged produced hs (andRight ht) ha hr
 have hl := OriginalHereditaryDeletionRowsLengthProof.appendSingletonLength size tailRow value singleValue produced
   (andLeft ht) hv hr
 exact completionIntro R (suc size) tagged (add headCount tailCount) produced (andIntro hl hrun)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsCore
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.VisitListCompletionConsCore
