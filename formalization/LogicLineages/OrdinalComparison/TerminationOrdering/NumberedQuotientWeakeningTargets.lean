module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientWeakeningDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientWeakeningTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedPrimaryWeakening

def ActualCountedWeakeningReflection : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
    (q : Packed (Fin n) arity Gamma), InUniverse symbols S q.2 → ∀ (count target : Nat),
    CountedPath (QuotientEdge n arity symbols S above (sigma :: Gamma)) count
      (representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) q)) target →
    ∃ r : Packed (Fin n) arity Gamma, InUniverse symbols S r.2 ∧
      representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) r) = target ∧
      CountedPath (QuotientEdge n arity symbols S above Gamma) count (representativeCode symbols S q) (representativeCode symbols S r)

def ActualPositiveWeakeningReflection : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma : Ty)
    (q : Packed (Fin n) arity Gamma), InUniverse symbols S q.2 → ∀ target : Nat,
    PositivePath (QuotientEdge n arity symbols S above (sigma :: Gamma))
      (representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) q)) target →
    ∃ r : Packed (Fin n) arity Gamma, InUniverse symbols S r.2 ∧
      representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) r) = target ∧
      PositivePath (QuotientEdge n arity symbols S above Gamma) (representativeCode symbols S q) (representativeCode symbols S r)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientWeakeningTargets
