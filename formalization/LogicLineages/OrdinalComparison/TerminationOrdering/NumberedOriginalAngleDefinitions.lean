module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationPathProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngle
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax

def transportAux {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {sigma tau : Ty}
    (h : sigma=tau) (Q : AuxTerm Symbol arity Gamma sigma) : AuxTerm Symbol arity Gamma tau :=
  Eq.mp (congrArg (AuxTerm Symbol arity Gamma) h) Q

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalAngle
