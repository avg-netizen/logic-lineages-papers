module

public import LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowLogicalAxiomCode
open GorbowSyntax GorbowPACore
open LogicLineages.ComputabilityKnowledge.GorbowLogicalAxiomCode

def GuardCalibration : Prop :=
  (∀ n count args, guardFormulas n count args = true ↔ args.length = count ∧
    ∀ raw ∈ args, ∃ φ : Formula n, raw = GorbowFormulaPrefixCode.encode φ) ∧
  (∀ n count args, guardTerms n count args = true ↔ args.length = count ∧
    ∀ raw ∈ args, ∃ t : Term n, raw = GorbowTermPrefixCode.encode t)

def ExactCompilation : Prop := ∀ n annotation out, compile n annotation = some out ↔
  ∃ w : LogicalInstance n, annotation = encode w ∧ out = GorbowFormulaPrefixCode.encode (logicalFormula w)

def AnnotationInjection : Prop := ∀ n : Nat, Function.Injective (@encode n)

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × Nat × List (List Nat) => guardFormulas p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List (List Nat) => guardTerms p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Annotation => compile p.1 p.2)

def Target : Prop := GuardCalibration ∧ ExactCompilation ∧ AnnotationInjection ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowLogicalAxiomCode
