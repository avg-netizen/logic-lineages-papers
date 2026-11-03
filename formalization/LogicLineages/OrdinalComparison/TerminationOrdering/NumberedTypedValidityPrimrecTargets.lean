module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericTypedValidationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedValidityPrimrecTargets
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedNumericDecoding

def ActualTermSuccessPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × Ty × Code (Fin n) =>
      (decodeTerm arity p.1 p.2.1 p.2.2).isSome)

def ActualArgumentsSuccessPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × List Ty × Code (Fin n) =>
      (decodeArguments arity p.1 p.2.1 p.2.2).isSome)

def ActualNumericTermSuccessPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × Ty × Nat =>
      ((decodeCode n p.2.2).bind (decodeTerm arity p.1 p.2.1)).isSome)

def ActualNumericArgumentsSuccessPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × List Ty × Nat =>
      ((decodeCode n p.2.2).bind (decodeArguments arity p.1 p.2.1)).isSome)

def ActualNumericPackedSuccessPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    Primrec (fun p : List Ty × Nat =>
      (decodePackedNumber n arity p.1 p.2).isSome)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedValidityPrimrecTargets
