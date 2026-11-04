module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakening
open Source NumberedRewriteSyntax NumberedRewriteReduction

def renamePacked {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (rho : Renaming Gamma Delta) (q : Packed Symbol arity Gamma) : Packed Symbol arity Delta :=
  ⟨q.1,NumberedRewriteSyntax.rename q.2 rho⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimaryWeakening
