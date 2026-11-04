module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceApplicativeSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceInertSpineComputabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedSubstitutionCompositionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironment
open Source NumberedRewriteSyntax
/-- Extend an actual typed substitution by the supplied argument. -/
def extend {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {sigma : Ty}
    (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (a : AuxTerm Symbol arity Delta sigma) :
    NumberedRewriteSyntax.Substitution Symbol arity (sigma :: Gamma) Delta := fun v => match v with
  | .here => a
  | .there w => theta w
end LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaEnvironment
