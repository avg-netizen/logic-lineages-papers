module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryContextStabilityTargets
open Source Source.SourceMarkedSyntax RecursiveComparison LiteralContexts ConfinedOrdinarySubstitution

def WeakContextClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Delta Gamma : List Ty) (upsilon tau : Ty) (C : Context Symbol arity Delta upsilon Gamma tau)
    (s t : Term Symbol arity Delta upsilon),
  Weak Symbol arity above Delta ⟨upsilon,embed s⟩ ⟨upsilon,embed t⟩ →
    Weak Symbol arity above Gamma ⟨tau,embed (plug C s)⟩ ⟨tau,embed (plug C t)⟩

def BothConfinedContextClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (Delta Gamma : List Ty) (upsilon tau : Ty) (C : Context Symbol arity Delta upsilon Gamma tau)
    (s t : Term Symbol arity Delta upsilon),
  (ConfinedWeak above s t → ConfinedWeak above (plug C s) (plug C t)) ∧
  (ConfinedStrict above s t → ConfinedStrict above (plug C s) (plug C t))

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryContextStabilityTargets
