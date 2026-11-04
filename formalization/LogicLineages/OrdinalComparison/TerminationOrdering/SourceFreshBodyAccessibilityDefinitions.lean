module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationBindingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibility
open Source NumberedRewriteSyntax

def freshInstance {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (body : AuxTerm Symbol arity (sigma :: Gamma) tau) : AuxTerm Symbol arity (sigma :: Gamma) tau :=
  substitute (NumberedRewriteSyntax.rename body (Renaming.lift (Renaming.weaken Gamma sigma)))
    (singleSubstitution (.var .here))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceFreshBodyAccessibility
