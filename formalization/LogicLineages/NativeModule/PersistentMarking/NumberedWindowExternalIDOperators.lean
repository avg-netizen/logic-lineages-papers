module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowArithmeticDirectCodeTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalIDOperators
open Spine NumberedWindowArithmeticAllContextTargets
open NumberedWindowArithmeticDirectCodeTargets

abbrev Pred := Nat → Prop
abbrev Operator := Pred → Pred

/-- The ordinary external typed accessibility clause on a known
independent domain and source-to-descendant relation. -/
def guardedStep (domain : Pred) (descends : Nat → Nat → Prop) : Operator :=
  fun P n => domain n ∧ ∀ m, descends n m → P m

def scalarStep (S : Signature) (K : List Ty) : Operator :=
  guardedStep (AdmittedAddress S K) (AddressPositive S K)

def multisetStep (S : Signature) (K : List Ty) : Operator :=
  guardedStep (AdmittedAddressListCode S K) (DirectAtCode S K)

def tagScalar (n : Nat) : Nat := 2 * n
def tagMultiset (n : Nat) : Nat := 2 * n + 1

/-- The two clauses are independent. Each consults only its own tag
and keeps its actual existing typed domain and relation. -/
def taggedStep (S : Signature) (K : List Ty) : Operator := fun P n =>
  (∃ x, n = tagScalar x ∧ scalarStep S K (fun y => P (tagScalar y)) x) ∨
  (∃ x, n = tagMultiset x ∧ multisetStep S K (fun y => P (tagMultiset y)) x)

def Below (P Q : Pred) : Prop := ∀ n, P n → Q n
def IsMonotone (F : Operator) : Prop := ∀ P Q, Below P Q → Below (F P) (F Q)
def IsPrefixed (F : Operator) (P : Pred) : Prop := Below (F P) P

/-- External intersection of all pre-fixed predicates. Nothing here
asserts that an arbitrary valid code is accessible or internally provable. -/
def Least (F : Operator) : Pred := fun n => ∀ P, IsPrefixed F P → P n

end LogicLineages.PersistentMarking.NumberedWindowExternalIDOperators
