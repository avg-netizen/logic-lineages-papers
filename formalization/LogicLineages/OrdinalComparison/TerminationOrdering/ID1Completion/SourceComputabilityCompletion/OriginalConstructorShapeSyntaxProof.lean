module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open OriginalConstructorShape InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)

theorem markGraphRename {alpha beta : Type} (value input : OTerm alpha) (j : alpha → beta) :
    (markGraph value input).relabel j = markGraph (value.relabel j) (input.relabel j) :=
  graph1Rename mark value input j

theorem tagGraphRename {alpha beta : Type} (value input : OTerm alpha) (j : alpha → beta) :
    (tagGraph value input).relabel j = tagGraph (value.relabel j) (input.relabel j) :=
  graph1Rename tag value input j

theorem applicationShapeRename {alpha beta : Type} (domain input : OTerm alpha) (j : alpha → beta) :
    (applicationShape domain input).relabel j = applicationShape (domain.relabel j) (input.relabel j) := by
  simp only [applicationShape,conjunctionRename,tagGraphRename,graph1Rename,positionTermRename]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalConstructorShapeSyntaxProof
