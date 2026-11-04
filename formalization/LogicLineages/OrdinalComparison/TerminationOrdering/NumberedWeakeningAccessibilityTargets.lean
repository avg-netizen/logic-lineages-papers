module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWeakeningAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWeakeningAccessibilityTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedPrimaryWeakening

def ActualWeakeningAccessibilityForward : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
    (q : Packed (Fin n) arity Gamma), InUniverse symbols S q.2 →
    Acc (fun y x => PositivePath (QuotientEdge n arity symbols S above Gamma) x y) (representativeCode symbols S q) →
    Acc (fun y x => PositivePath (QuotientEdge n arity symbols S above (sigma :: Gamma)) x y)
      (representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) q))

def ActualWeakeningAccessibilityBackward : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
    (q : Packed (Fin n) arity Gamma), InUniverse symbols S q.2 →
    Acc (fun y x => PositivePath (QuotientEdge n arity symbols S above (sigma :: Gamma)) x y)
      (representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) q)) →
    Acc (fun y x => PositivePath (QuotientEdge n arity symbols S above Gamma) x y) (representativeCode symbols S q)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedWeakeningAccessibilityTargets
