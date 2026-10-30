module

public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowInstanceCode
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowInstanceCode

def ExactInstance : Prop := ∀ n raw traw out, instanceCode n raw traw = some out ↔
  ∃ (φ : Formula (n+1)) (t : Term n), raw = GorbowFormulaPrefixCode.encode φ ∧
    traw = GorbowTermPrefixCode.encode t ∧ out = GorbowFormulaPrefixCode.encode (GorbowStandardInstances.instantiate φ t)

def ExactWeakening : Prop := ∀ n raw out, weakeningCode n raw = some out ↔
  ∃ φ : Formula n, raw = GorbowFormulaPrefixCode.encode φ ∧ out = GorbowFormulaPrefixCode.encode (GorbowPACore.weaken φ)

def ExactSuccessor : Prop := ∀ n raw out, successorCode n raw = some out ↔
  ∃ φ : Formula (n+1), raw = GorbowFormulaPrefixCode.encode φ ∧ out = GorbowFormulaPrefixCode.encode (GorbowStandardInduction.successorInstance φ)

def ExactInduction : Prop := ∀ n raw out, inductionCode n raw = some out ↔
  ∃ φ : Formula (n+1), raw = GorbowFormulaPrefixCode.encode φ ∧ out = GorbowFormulaPrefixCode.encode (GorbowStandardInduction.inductionAxiom φ)

def ExactRejection : Prop :=
  (∀ n raw traw, instanceCode n raw traw = none ↔
    GorbowFormulaPrefixCode.decode (n+1) raw = none ∨ GorbowTermPrefixCode.decode n traw = none) ∧
  (∀ n raw, weakeningCode n raw = none ↔ GorbowFormulaPrefixCode.decode n raw = none) ∧
  (∀ n raw, successorCode n raw = none ↔ GorbowFormulaPrefixCode.decode (n+1) raw = none) ∧
  (∀ n raw, inductionCode n raw = none ↔ GorbowFormulaPrefixCode.decode (n+1) raw = none)

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat => variableDictionary p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat × List Nat => instanceCode p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × List Nat => weakeningCode p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => successorCode p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => inductionCode p.1 p.2)

def Target : Prop := ExactInstance ∧ ExactWeakening ∧ ExactSuccessor ∧ ExactInduction ∧ ExactRejection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowInstanceCode
