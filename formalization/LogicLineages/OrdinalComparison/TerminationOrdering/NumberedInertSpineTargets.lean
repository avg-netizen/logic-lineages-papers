module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedWindowReduction NumberedInertSpine

def ActualPrimaryInertInvariant : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (q r : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r →
    (InertSpine q.2 ↔ InertSpine r.2) ∧ inertRank q.2 = inertRank r.2

def ActualStepInertDecrease : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r → InertSpine q →
    InertSpine r ∧ inertRank r < inertRank q

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineTargets
