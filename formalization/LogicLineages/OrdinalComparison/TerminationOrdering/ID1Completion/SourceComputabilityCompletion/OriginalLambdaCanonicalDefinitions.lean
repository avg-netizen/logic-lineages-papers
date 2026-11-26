module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryLambdaBodyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonical
open Source NumberedRewriteSyntax NumberedRewriteReduction

/-- The ORIGINAL typed lambda packed in Gamma, with its body in the ORIGINAL
extended context sigma::Gamma. This only names an existing source constructor;
it changes no term, type, label, primary class or numbering. -/
def lambdaPacked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    {sigma tau : Ty} (body : AuxTerm Symbol arity (sigma :: Gamma) tau) :
    Packed Symbol arity Gamma :=
  ⟨.arrow sigma tau,AuxTerm.lam body⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCanonical
