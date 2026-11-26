module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative
open SourceZeroNumberedComputability
open NumberedHereditaryView

def ExactRootSignature : Prop :=
 ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
 SubtypeClosed (fun t => t ∈ S) → ∀ (q r : Packed (Fin n) arity Gamma),
 InUniverse symbols S q.2 → InUniverse symbols S r.2 →
 (rootSignature symbols S q = rootSignature symbols S r ↔ WindowPrimary (Fin n) arity symbols S Gamma q r)

def ExactFiniteDepth : Prop :=
 ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
 SubtypeClosed (fun t => t ∈ S) → ∀ (depth : Nat) (q r : Packed (Fin n) arity Gamma),
 InUniverse symbols S q.2 → InUniverse symbols S r.2 →
 (HereditaryView symbols S depth q r ↔ WindowPrimary (Fin n) arity symbols S Gamma q r)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedHereditaryViewTargets
