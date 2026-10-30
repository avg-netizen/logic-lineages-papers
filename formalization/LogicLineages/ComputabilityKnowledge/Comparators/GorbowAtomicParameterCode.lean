module

public import LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicParameterCode
open GorbowSyntax GorbowAtomicParameters GorbowNameDictionary
open LogicLineages.ComputabilityKnowledge.GorbowAtomicParameterCode

def SlotCalibration : Prop := ∀ n m (names : Fin n → Fin m) (i : Fin m),
  codeSlot (namesList names) i.val=GorbowTermPrefixCode.encode (codeDictionary names i) ∧
  valueSlot (namesList names) i.val=GorbowTermPrefixCode.encode (valueDictionary names i)

def DictionaryCalibration : Prop := ∀ n m (names : Fin n → Fin m),
  codeSlots m (namesList names)=List.ofFn (fun i => GorbowTermPrefixCode.encode (codeDictionary names i)) ∧
  valueSlots m (namesList names)=GorbowLiftedDictionary.dictionary (valueDictionary names)

def InstanceCalibration : Prop := ∀ n m (R : Formula m) (names : Fin n → Fin m),
  instanceRaw m (GorbowFormulaPrefixCode.encode R) (namesList names)=
    GorbowTermPrefixCode.encode (GorbowAtomicTruth.instanceCodeTerm R names)

def UniformPrograms : Prop :=
  Primrec (fun p : List Nat × Nat => codeSlot p.1 p.2) ∧
  Primrec (fun p : List Nat × Nat => valueSlot p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => codeSlots p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => valueSlots p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => instanceRaw p.1 p.2.1 p.2.2)

def Target : Prop := SlotCalibration ∧ DictionaryCalibration ∧ InstanceCalibration ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowAtomicParameterCode
