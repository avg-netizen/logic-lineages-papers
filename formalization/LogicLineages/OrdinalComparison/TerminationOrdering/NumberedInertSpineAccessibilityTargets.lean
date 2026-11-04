module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineAccessibilityTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowTraces NumberedLeastCodeRepresentative NumberedQuotientPaths NumberedInertSpine

def ActualTraceInertBound : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (above : Symbol → Symbol → Prop)
    (Gamma : List Ty) (count : Nat) (q r : Packed Symbol arity Gamma),
    WindowTrace Symbol arity symbols S above Gamma count q r → InertSpine q.2 →
    InertSpine r.2 ∧ inertRank r.2 + count ≤ inertRank q.2

def ActualQuotientInertAccessibility : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (tau : Ty)
      (q : AuxTerm (Fin n) arity Gamma tau), InUniverse symbols S q → InertSpine q →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S ⟨tau,q⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInertSpineAccessibilityTargets
