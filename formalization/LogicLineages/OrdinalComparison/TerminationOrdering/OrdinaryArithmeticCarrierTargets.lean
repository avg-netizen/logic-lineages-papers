module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierTargets
open OrdinaryArithmeticCarrier

def ActualCarrierCheckersPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), Primrec (scalarValue n arity Gamma) ∧ Primrec (listValue n arity Gamma)

def EncodedCarrierFormulas : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), ∃ scalar list : OrdinaryArithmetic.Formula (Fin 2), ∀ context value : Nat, (scalar.Realize ![context,value] ↔ encodedScalar n arity Gamma context value) ∧ (list.Realize ![context,value] ↔ encodedList n arity Gamma context value)

def ActualTypedCarrierFormulas : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Source.Ty), ∃ scalar list : OrdinaryArithmetic.Formula (Fin 2), ∀ (symbols : List (Fin n)) (S : List Source.Ty), SubtypeClosed (fun tau => tau ∈ S) → ∀ (table : Fin n → Fin n → Bool) (x : Nat) (values : List Nat), (scalar.Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,x] ↔ ∃ q : NumberedRewriteReduction.Packed (Fin n) arity Gamma, NumberedFiniteUniverse.InUniverse symbols S q.2 ∧ NumberedLeastCodeRepresentative.representativeCode symbols S q = x) ∧ (list.Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,Encodable.encode values] ↔ ∀ y ∈ values, ∃ q : NumberedRewriteReduction.Packed (Fin n) arity Gamma, NumberedFiniteUniverse.InUniverse symbols S q.2 ∧ NumberedLeastCodeRepresentative.representativeCode symbols S q = y)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticCarrierTargets
