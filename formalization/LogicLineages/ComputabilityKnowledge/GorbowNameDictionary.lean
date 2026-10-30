module

public import LogicLineages.ComputabilityKnowledge.GorbowFormulaComposition
public import Mathlib.Data.Fintype.Fin

@[expose] public section
/-! Explicit arbitrary free-name enumeration, not ambient arity as precise
support. The finite search dictionary uses zero only at unused names. -/
namespace LogicLineages.ComputabilityKnowledge.GorbowNameDictionary
open GorbowSyntax GorbowFreeSupport

def namesList {n m : Nat} (names : Fin n → Fin m) : List Nat :=
  List.ofFn (fun j => (names j).val)

def Covers {n m : Nat} (R : Formula m) (names : Fin n → Fin m) : Prop :=
  formulaSupport R=Finset.univ.image (fun j => (names j).val)

def dictionary {n m k : Nat} (names : Fin n → Fin m) (values : Fin n → Term k) : Fin m → Term k :=
  fun i => (List.ofFn values).getD ((namesList names).idxOf i.val) .zero
end LogicLineages.ComputabilityKnowledge.GorbowNameDictionary
