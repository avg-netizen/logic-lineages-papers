module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRepeatProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalAcceptanceConjunctionProof (constantZeroValue)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaDirectBottomTrace

theorem rejectZero : OriginalLambdaDirectBottomTraceTargets.RejectZero := by
 intro source leaf body alpha Delta
 constructor
 · exact InternalAcceptanceBranchProof.zeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1)
    _ z (Fin.cons z Fin.elim0) (projectionValue 0 (Fin.cons z Fin.elim0))
    (constantZeroValue (Fin.cons z Fin.elim0))
 · exact InternalAcceptanceBranchProof.zeroBranchIntro (.projection 0) (InternalAcceptance.constantZero 1)
    _ z (Fin.cons z Fin.elim0) (projectionValue 0 (Fin.cons z Fin.elim0))
    (constantZeroValue (Fin.cons z Fin.elim0))

theorem repeatNil : OriginalLambdaDirectBottomTraceTargets.RepeatNil := by
 intro source leaf body alpha out initial
 exact InternalRawListRepeatProof.actualOriginalRawListRepeatZero body (transition source leaf) alpha out initial

theorem repeatFront : OriginalLambdaDirectBottomTraceTargets.RepeatFront := by
 intro source leaf body alpha code head tail out initial next
 exact InternalRawListRepeatProof.actualOriginalRawListRepeatFrontCons body (transition source leaf) alpha code head tail out initial next
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceProof
