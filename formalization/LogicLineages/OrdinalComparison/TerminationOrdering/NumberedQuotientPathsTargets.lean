module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedWindowEquivalence NumberedWindowTraces NumberedLeastCodeRepresentative NumberedQuotientPaths

def ActualEdgeCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
  InUniverse symbols S q.2 → InUniverse symbols S r.2 →
  (QuotientEdge n arity symbols S above Gamma (representativeCode symbols S q) (representativeCode symbols S r) ↔
    ∃ (tau : Ty) (a b : AuxTerm (Fin n) arity Gamma tau),
      WindowPrimary (Fin n) arity symbols S Gamma q ⟨tau,a⟩ ∧
      WindowStep (Fin n) arity symbols S above Gamma tau a b ∧
      WindowPrimary (Fin n) arity symbols S Gamma ⟨tau,b⟩ r)

def ActualCountedForward : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (count : Nat) (q r : Packed (Fin n) arity Gamma),
  InUniverse symbols S q.2 → WindowTrace (Fin n) arity symbols S above Gamma count q r →
  CountedPath (QuotientEdge n arity symbols S above Gamma) count (representativeCode symbols S q) (representativeCode symbols S r)

def ActualCountedBackward : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (count : Nat) (q r : Packed (Fin n) arity Gamma),
  InUniverse symbols S q.2 → InUniverse symbols S r.2 →
  CountedPath (QuotientEdge n arity symbols S above Gamma) count (representativeCode symbols S q) (representativeCode symbols S r) →
  WindowTrace (Fin n) arity symbols S above Gamma count q r

def ActualPositiveClosure : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (above : Fin n → Fin n → Prop) (Gamma : List Ty) (x y : Nat),
  PositivePath (QuotientEdge n arity symbols S above Gamma) x y ↔
    ∃ count,0<count ∧ CountedPath (QuotientEdge n arity symbols S above Gamma) count x y

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsTargets
