module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierTargets
open Source OrdinaryArithmeticTypedCarrier NumberedTypedCarrier

def ActualTypedCheckerPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (fun p : (List (Fin n) × List Ty) × Ty × Nat =>
    typedCanonicalCarrierTest n arity p.1.1 p.1.2 Gamma p.2.1 p.2.2)

def ActualEncodedTypedPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  Primrec (typedValue n arity Gamma)

def ActualTypedArithmeticFormula : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ phi : OrdinaryArithmetic.Formula (Fin 3),
    (∀ context typ value : Nat, phi.Realize ![context,typ,value] ↔ encodedTyped n arity Gamma context typ value) ∧
    (∀ (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun tau => tau ∈ S) →
      ∀ (table : Fin n → Fin n → Bool) (tau : Ty) (value : Nat),
      phi.Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,NumberedLeastCodeRepresentative.typeNumber tau,value] ↔
        ∃ q : NumberedRewriteReduction.Packed (Fin n) arity Gamma, NumberedFiniteUniverse.InUniverse symbols S q.2 ∧
          q.1 = tau ∧ NumberedLeastCodeRepresentative.representativeCode symbols S q = value)

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryArithmeticTypedCarrierTargets
