module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitution
open Source NumberedRewriteSyntax NumberedRewriteReduction

def substitutePacked {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (rho : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta) (q : Packed Symbol arity Gamma) :
    Packed Symbol arity Delta := ⟨q.1,NumberedRewriteSyntax.substitute q.2 rho⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitution
