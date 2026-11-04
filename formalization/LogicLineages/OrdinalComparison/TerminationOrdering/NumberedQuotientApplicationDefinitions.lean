module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplication
open Source NumberedRewriteSyntax NumberedRewriteReduction

def applicationPacked {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (f : AuxTerm Symbol arity Gamma (.arrow sigma tau)) (a : AuxTerm Symbol arity Gamma sigma) : Packed Symbol arity Gamma :=
  ⟨tau,AuxTerm.app f a⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplication
