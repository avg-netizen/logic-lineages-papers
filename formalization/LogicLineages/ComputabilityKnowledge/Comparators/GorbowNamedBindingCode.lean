module

public import LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCode
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedBindingCode
open GorbowSyntax GorbowFreeSupport GorbowNamedBinding
open LogicLineages.ComputabilityKnowledge.GorbowNamedBindingCode

def DictionaryCalibration : Prop := ∀ n (v : Fin n),
  bindDictionaryCode n v.val=GorbowLiftedDictionary.dictionary (bindDictionary v) ∧
  selectDictionaryCode n v.val=GorbowLiftedDictionary.dictionary (selectDictionary v)

def ExactBinding : Prop := ∀ n v raw out,
  (bindAllCode n v raw=some out ↔ ∃ (hv : v<n) (φ : Formula n),
    raw=GorbowFormulaPrefixCode.encode φ ∧ out=GorbowFormulaPrefixCode.encode (bindAll ⟨v,hv⟩ φ)) ∧
  (bindExCode n v raw=some out ↔ ∃ (hv : v<n) (φ : Formula n),
    raw=GorbowFormulaPrefixCode.encode φ ∧ out=GorbowFormulaPrefixCode.encode (bindEx ⟨v,hv⟩ φ))

def ExactSelection : Prop := ∀ n v raw out,
  selectCode n v raw=some out ↔ ∃ (hv : v<n) (φ : Formula n),
    raw=GorbowFormulaPrefixCode.encode φ ∧ formulaSupport φ={v} ∧
    out=GorbowFormulaPrefixCode.encode (selectVariable ⟨v,hv⟩ φ)

def SelectedOutput : Prop := ∀ n v raw out, selectCode n v raw=some out →
  ∃ A : Selector, out=GorbowFormulaPrefixCode.encode A.val

def MalformedRejection : Prop := ∀ n v raw,
  (¬ v<n ∨ GorbowSyntaxValidation.validFormula n raw=false) →
  bindAllCode n v raw=none ∧ bindExCode n v raw=none ∧ selectCode n v raw=none

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => bindDictionaryCode p.1 p.2) ∧
  Primrec (fun p : Nat × Nat => selectDictionaryCode p.1 p.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => bindAllCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => bindExCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => selectCode p.1 p.2.1 p.2.2)

def Target : Prop := DictionaryCalibration ∧ ExactBinding ∧ ExactSelection ∧ SelectedOutput ∧ MalformedRejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowNamedBindingCode
