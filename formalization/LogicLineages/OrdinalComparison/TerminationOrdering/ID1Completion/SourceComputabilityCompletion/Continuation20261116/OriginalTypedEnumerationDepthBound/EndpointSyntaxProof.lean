module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.SyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.EndpointSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalTagArithmeticSyntaxProof (sucRelabel)
open InternalOriginalOrderSyntaxProof (orderRename addRelabel)

theorem termRename {alpha beta : Type} (d s : OTerm alpha) (j : alpha → beta) :
    (termBound d s).relabel j = termBound (d.relabel j) (s.relabel j) := by
  simp only [termBound,twice,InternalLessThan.strictLess,orderRename,sucRelabel,addRelabel]

theorem argumentsRename {alpha beta : Type} (d s : OTerm alpha) (j : alpha → beta) :
    (argumentsBound d s).relabel j = argumentsBound (d.relabel j) (s.relabel j) := by
  simp only [argumentsBound,twice,InternalLessThan.strictLess,orderRename,sucRelabel,addRelabel]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.EndpointSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.EndpointSyntaxProof
