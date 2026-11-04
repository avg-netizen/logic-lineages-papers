module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientSubstitutionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientSubstitutionTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedUniverseBindingTargets
open NumberedPrimarySubstitution NumberedLeastCodeRepresentative NumberedQuotientPaths

def ActualCountedQuotientSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta) (q r : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → InUniverse symbols S r.2 →
    GoodSubstitution (fun t => t ∈ S) (HeadInWindow arity symbols S) theta →
    ∀ count : Nat, CountedPath (QuotientEdge n arity symbols S above Gamma) count
      (representativeCode symbols S q) (representativeCode symbols S r) →
    ∃ m : Nat, m ≤ count ∧ CountedPath (QuotientEdge n arity symbols S above Delta) m
      (representativeCode symbols S (substitutePacked theta q)) (representativeCode symbols S (substitutePacked theta r))

def ActualPositiveQuotientSubstitution : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma Delta : List Ty)
    (theta : NumberedRewriteSyntax.Substitution (Fin n) arity Gamma Delta) (q r : Packed (Fin n) arity Gamma),
    InUniverse symbols S q.2 → InUniverse symbols S r.2 →
    GoodSubstitution (fun t => t ∈ S) (HeadInWindow arity symbols S) theta →
    PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S q) (representativeCode symbols S r) →
    representativeCode symbols S (substitutePacked theta q) = representativeCode symbols S (substitutePacked theta r) ∨
    PositivePath (QuotientEdge n arity symbols S above Delta)
      (representativeCode symbols S (substitutePacked theta q)) (representativeCode symbols S (substitutePacked theta r))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientSubstitutionTargets
