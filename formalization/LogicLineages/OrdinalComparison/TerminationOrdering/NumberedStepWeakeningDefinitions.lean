module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepRenamingProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakening
open Source NumberedRewriteSyntax

def retractionFiller (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) (sigma : Ty) : AuxTerm Symbol arity Gamma sigma :=
  .app (.bottom (.arrow sigma sigma)) (.bottom sigma)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepWeakening
