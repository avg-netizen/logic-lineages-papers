module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence NumberedWindowReduction NumberedBottomSpine

def ActualPrimarySpineInvariant : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S Gamma : List Ty) (q r : Packed Symbol arity Gamma),
    WindowPrimary Symbol arity symbols S Gamma q r →
    (BottomSpine q.2 ↔ BottomSpine r.2) ∧ spineDepth q.2 = spineDepth r.2

def ActualStepSpineDecrease : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
    WindowStep Symbol arity symbols S above Gamma tau q r → BottomSpine q →
    BottomSpine r ∧ spineDepth r < spineDepth q

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineTargets
