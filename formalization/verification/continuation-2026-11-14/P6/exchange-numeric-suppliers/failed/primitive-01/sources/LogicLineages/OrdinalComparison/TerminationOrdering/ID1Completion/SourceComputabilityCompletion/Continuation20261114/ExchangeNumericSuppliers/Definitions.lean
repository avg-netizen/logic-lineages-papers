module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeGraphRecursion.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers
abbrev Node (n : Nat) := NumberedAuxiliaryCoding.Code (Fin n) × NumberedAuxiliaryCoding.Code (Fin n)
abbrev Window (n : Nat) := List (Fin n) × List Source.Ty
/-- Explicit numeric extension of the original source rank; invalid nodes have rank zero. -/
def rankAt (n : Nat) (node : Nat) (_param : Nat) : Nat :=
  ((Encodable.decode (α := Node n) node).map
    (fun p => NumberedLeastCodeRepresentative.codeNumber p.1)).getD 0
/-- Exact ordered dependency codes. Invalid nodes have no dependencies. -/
def depsAt (n : Nat) (node : Nat) (_param : Nat) : List Nat :=
  ((Encodable.decode (α := Node n) node).map
    (fun p => (NumberedExchangeCodeFieldsProof.dependencies p).map Encodable.encode)).getD []
/-- Numeric recursive values are 0/1; arbitrary numeric answers are interpreted by
exact-one Bool conversion, with the original layer's missing-slot defaults. -/
def layerAt (n : Nat) (arity : Fin n → Nat) (node : Nat) (answers : List Nat) (param : Nat) : Option Nat :=
  some (match Encodable.decode (α := Node n) node, Encodable.decode (α := Window n) param with
  | some p, some window =>
    (NumberedExchangeCodePrimrecProof.layer n arity
      (window,NumberedExchangeCodeFieldsProof.fields p.1,NumberedExchangeCodeFieldsProof.fields p.2,
        answers.map (fun value => value == 1))).toNat
  | _, _ => 0)
/-- Original codeExchange on decoded nodes/windows, with an explicit zero extension. -/
def valueAt (n : Nat) (arity : Fin n → Nat) (node param : Nat) : Nat :=
  match Encodable.decode (α := Node n) node, Encodable.decode (α := Window n) param with
  | some p, some window => (NumberedExchangeCode.codeExchange arity window.1 window.2 p.1 p.2).toNat
  | _, _ => 0
def rankValue (n : Nat) (v : List.Vector Nat 2) : Nat := rankAt n (v.get 0) (v.get 1)
def depsValue (n : Nat) (v : List.Vector Nat 2) : Nat :=
  NumberedMultisetNumeric.numbersNumber (depsAt n (v.get 0) (v.get 1))
def layerValue (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 3) : Nat :=
  Encodable.encode (layerAt n arity (v.get 0)
    ((NumberedMultisetNumeric.decodeNumbers (v.get 1)).getD []) (v.get 2))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeNumericSuppliers
