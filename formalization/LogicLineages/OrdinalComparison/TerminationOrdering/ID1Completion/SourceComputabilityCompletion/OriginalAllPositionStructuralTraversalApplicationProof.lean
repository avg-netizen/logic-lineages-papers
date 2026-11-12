module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalSourceProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyApplicationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalApplicationProof
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalAllPositionStructuralTraversalDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem actualApplicationLaw :
    OriginalAllPositionStructuralTraversalApplicationTargets.ActualApplicationLaw := by
  intro p H G W P
  dsimp only
  intro body alpha Delta input out typ parameter arrow d e fn arg fnOut argOut fValue aValue mark cutoff
    hRange hp hfp hap harrow _fields hi ho hfk hfok hak haok
  have hout := OriginalLambdaTraversalOutputProof.invariantAtInput
    (refined p H G W P).base (refined p H G W P).window out input typ parameter hp
  have hfout := OriginalLambdaTraversalOutputProof.invariantAtInput
    (refined p H G W P).base (refined p H G W P).window fnOut fn arrow parameter hfp
  have haout := OriginalLambdaTraversalOutputProof.invariantAtInput
    (refined p H G W P).base (refined p H G W P).window argOut arg d parameter hap
  have hw := andLeft hp
  rw [OriginalAllPositionStructuralTraversalSourceProof.window] at hw
  exact OriginalPositionStructuralKeyApplicationProof.actualApplication p H G W body alpha Delta
    input out d e arrow fn arg fnOut argOut parameter cutoff fValue aValue mark
    hRange hw
    (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P input parameter (andLeft (andLeft (andRight hp))))
    (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P out parameter (andLeft hout))
    (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P fn parameter (andLeft (andLeft (andRight hfp))))
    (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P arg parameter (andLeft (andLeft (andRight hap))))
    (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P fnOut parameter (andLeft hfout))
    (OriginalAllPositionStructuralTraversalSourceProof.sourceOfValidity p H G W P argOut parameter (andLeft haout))
    harrow (andRight (andLeft (andRight hfp))) (andLeft (andRight hfout))
    (andRight (andLeft (andRight hap))) (andLeft (andRight haout)) hi ho hfk hfok hak haok

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalApplicationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionStructuralTraversalApplicationProof
