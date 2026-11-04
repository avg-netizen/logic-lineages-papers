module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibilityTargets
open PositiveArithmeticOperators PositiveArithmeticLeastSet PositiveArithmeticAccessibility
open OrdinaryArithmeticCarrier OrdinaryArithmeticDirect SourceArithmeticAccessibility

def ActualEncodedScalarPreservation : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty) (context : Nat),
    DecodedSubtypeClosed n context →
    CarrierPreserved (encodedScalar n arity Gamma context) (encodedR n arity Gamma context)

def ActualEncodedListPreservation : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty) (context : Nat),
    DecodedSubtypeClosed n context →
    CarrierPreserved (encodedList n arity Gamma context) (encodedDirect n arity Gamma context)

def ActualSourceLeastAccessibility : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty),
    ∃ scalar multiset : Positive (Fin 2),
      (∀ context : Nat, Calibrates scalar context (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) ∧
        Calibrates multiset context (encodedList n arity Gamma context) (encodedDirect n arity Gamma context)) ∧
      (∀ context : Nat, DecodedSubtypeClosed n context → ∀ x : Nat,
        (x ∈ leastSet scalar context ↔ encodedScalar n arity Gamma context x ∧
          Acc (fun successor source => encodedR n arity Gamma context source successor) x) ∧
        (x ∈ leastSet multiset context ↔ encodedList n arity Gamma context x ∧
          Acc (fun successor source => encodedDirect n arity Gamma context source successor) x))

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceArithmeticAccessibilityTargets
