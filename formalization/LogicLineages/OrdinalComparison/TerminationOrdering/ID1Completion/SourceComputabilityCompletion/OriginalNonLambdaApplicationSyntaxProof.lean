module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open OriginalNonLambdaApplication

theorem nonLambdaRename {alpha beta : Type} (function : OTerm alpha) (j : alpha → beta) :
    (nonLambda function).relabel j = nonLambda (function.relabel j) := by
  change ((OriginalConstructorShape.tagGraph InternalOriginalStepGuard.one function).relabel j).not = _
  rw [OriginalConstructorShapeSyntaxProof.tagGraphRename]
  simp only [InternalOriginalStepGuard.one,sucRelabel,zRelabel]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNonLambdaApplicationSyntaxProof
