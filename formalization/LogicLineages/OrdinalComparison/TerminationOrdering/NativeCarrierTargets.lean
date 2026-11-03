module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierTargets
open Source LiteralContexts NativeCarrier

def BaseStrict : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (B : Ty) (K : Term Symbol arity [] (.arrow B B)) (U : Term Symbol arity [] B),
    ConfinedStrict above (carrier K U) U

def ApplicationClosure : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (above : Symbol → Symbol → Prop)
    (B : Ty) (P K : Term Symbol arity [] (.arrow B B)) (U T : Term Symbol arity [] B),
    ConfinedWeak above K P → ConfinedStrict above (carrier K U) T → ConfinedStrict above (carrier K U) (.app P T)

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierTargets
