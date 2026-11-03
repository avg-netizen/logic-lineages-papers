module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedAuxiliaryCoding NumberedLeastCodeRepresentative

def ActualStructuralNumberInjective : Prop := ∀ n,Function.Injective (@codeNumber n)

def ActualPackedNumberInjective : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Function.Injective (@packedNumber n arity Gamma)

def ActualRepresentativeAttained : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma),
  InUniverse symbols S q.2 → ∃ r,WindowPrimary (Fin n) arity symbols S Gamma q r ∧ representativeCode symbols S q=packedNumber r

def ActualRepresentativeMinimal : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
  InUniverse symbols S q.2 → WindowPrimary (Fin n) arity symbols S Gamma q r → representativeCode symbols S q≤packedNumber r

def ActualRepresentativeEquality : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q r : Packed (Fin n) arity Gamma),
  InUniverse symbols S q.2 → InUniverse symbols S r.2 →
  (representativeCode symbols S q=representativeCode symbols S r ↔ WindowPrimary (Fin n) arity symbols S Gamma q r)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLeastCodeRepresentativeTargets
