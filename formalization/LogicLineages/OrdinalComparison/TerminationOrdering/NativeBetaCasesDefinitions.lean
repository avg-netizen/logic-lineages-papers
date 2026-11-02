module
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCases
open Source

def caseTerm {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {τ : Ty}
    (u : Term Symbol arity Γ .ground) (A B : Term Symbol arity Γ τ) : Term Symbol arity Γ τ :=
  .app (.app (.app (.caseC τ) u) A) B

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCases
