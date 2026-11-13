module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnInternalStatementChecks
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationInternalProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationComplexProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open OriginalLambdaConstructorGraphSyntaxProof (queryCases)
open OriginalRawSyntaxTransportInternalVariableSupportProof (constantValue)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Only functionality of the actual return computation transports the independently
constructed observation to its actual runtime output. -/
theorem finish (Q : Program 2) (input parameter first second built returned : OTerm alpha)
    (hb : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot built input first second)))
    (hr : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned input first second)))
    (ho : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) built input parameter))) :
    Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation Q) returned input parameter)) := by
  exact outputTransport (OriginalRootObservation.rootObservation Q) built returned ![input,parameter]
    (valueUnique OriginalHereditaryReturn.returnRoot built returned ![input,first,second] hb hr) ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.ReturnSubstitutionProof.finish
