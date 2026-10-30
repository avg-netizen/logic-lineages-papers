module

public import LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation

@[expose] public section

namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowSyntaxValidation
open GorbowSyntax
open LogicLineages.ComputabilityKnowledge.GorbowSyntaxValidation

def ExactStack : Prop := ∀ tasks raw, scan tasks raw = some [] ↔ StackMeaning tasks raw

def ExactTypedDomain : Prop :=
  (∀ n raw, validTerm n raw = true ↔ ∃ t : Term n, GorbowTermPrefixCode.decode n raw = some t) ∧
  (∀ n raw, validFormula n raw = true ↔ ∃ φ : Formula n, GorbowFormulaPrefixCode.decode n raw = some φ)

def UniformPrograms : Prop :=
  Primrec (fun p : Task × Nat => expand p.1 p.2) ∧
  Primrec (fun p : State × Nat => step p.1 p.2) ∧
  Primrec (fun p : List Task × List Nat => scan p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => validTerm p.1 p.2) ∧
  Primrec (fun p : Nat × List Nat => validFormula p.1 p.2)

def Target : Prop := ExactStack ∧ ExactTypedDomain ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowSyntaxValidation
