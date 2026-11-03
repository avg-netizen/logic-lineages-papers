module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrier
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison LiteralContexts NativeRecursor

def unusedGroundStep {Symbol : Type} {arity : Symbol → Nat} {B : Ty}
    (K : Term Symbol arity [] (.arrow B B)) : Term Symbol arity [] (stepType B) :=
  .lam (K.rename (Renaming.weaken [] .ground))

def carrier {Symbol : Type} {arity : Symbol → Nat} {B : Ty}
    (K : Term Symbol arity [] (.arrow B B)) (U : Term Symbol arity [] B) : Term Symbol arity [] B :=
  recursorTerm .zeroC (unusedGroundStep K) U

def ConfinedWeak {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    {B : Ty} (K P : Term Symbol arity [] (.arrow B B)) : Prop :=
  Weak Symbol arity above [] ⟨.arrow B B,embed K⟩ ⟨.arrow B B,embed P⟩ ∧ typeSupport P ⊆ typeSupport K

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrier
