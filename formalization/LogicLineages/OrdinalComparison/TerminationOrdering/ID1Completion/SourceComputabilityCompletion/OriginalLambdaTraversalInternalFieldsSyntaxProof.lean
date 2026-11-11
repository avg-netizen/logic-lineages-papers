module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalCompletionOutputProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalPayloadArithmeticProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalLambdaTraversalInternal
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open InternalOriginalOrderSyntaxProof (addRelabel)

@[simp] theorem applicationFieldsRename {alpha beta : Type}
    (value d e fn arg : OTerm alpha) (j : alpha → beta) :
    (ApplicationFields value d e fn arg).relabel j =
      ApplicationFields (value.relabel j) (d.relabel j) (e.relabel j) (fn.relabel j) (arg.relabel j) := by
  simp only [ApplicationFields,conjunctionRename,graph1Rename,
    SourceComputabilityFormulaSupportProof.numeral,sucRelabel,zRelabel]

@[simp] theorem lambdaFieldsRename {alpha beta : Type}
    (value d e body parameter bodyParameter : OTerm alpha) (j : alpha → beta) :
    (LambdaFields value d e body parameter bodyParameter).relabel j =
      LambdaFields (value.relabel j) (d.relabel j) (e.relabel j) (body.relabel j)
        (parameter.relabel j) (bodyParameter.relabel j) := by
  simp only [LambdaFields,conjunctionRename,graph1Rename,graph2Rename,
    InternalOriginalStepGuard.one,sucRelabel,zRelabel]

@[simp] theorem childFuelSumRename {alpha beta : Type} (fp ap : OTerm alpha) (j : alpha → beta) :
    (InternalPairingSumBounds.childFuelSum fp ap).relabel j =
      InternalPairingSumBounds.childFuelSum (fp.relabel j) (ap.relabel j) := by
  simp only [InternalPairingSumBounds.childFuelSum,addRelabel,sucRelabel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalInternalFieldsSyntaxProof
