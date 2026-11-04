module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineAccessibilityTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowTraces NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedBottomSpine

def ActualTraceSpineBound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (count : Nat) (q r : Packed Symbol arity Gamma),
    WindowTrace Symbol arity symbols S above Gamma count q r → BottomSpine q.2 →
    BottomSpine r.2 ∧ spineDepth r.2 + count ≤ spineDepth q.2

def ActualQuotientSpineAccessibility : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (tau : Ty)
      (q : AuxTerm (Fin n) arity Gamma tau), InUniverse symbols S q → BottomSpine q →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S ⟨tau,q⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomSpineAccessibilityTargets
