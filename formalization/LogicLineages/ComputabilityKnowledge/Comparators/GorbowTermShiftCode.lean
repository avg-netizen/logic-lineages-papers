module

public import LogicLineages.ComputabilityKnowledge.GorbowTermShiftCode

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermShiftCode
open GorbowSyntax GorbowSyntaxValidation
open LogicLineages.ComputabilityKnowledge.GorbowTermShiftCode

def ScannerInvariant : Prop :=
  ∀ (n b : Nat) (t : Term n) (tasks : List Task) (acc : List Nat),
    (GorbowTermPrefixCode.encode t).foldl (shiftStep b) (some ((0,n)::tasks),acc) =
      (some tasks, acc ++ GorbowTermPrefixCode.encode (shiftTerm b t))

def ExactOutput : Prop :=
  ∀ n b raw out, shiftCode n b raw = some out ↔ ∃ t : Term n,
    raw = GorbowTermPrefixCode.encode t ∧ out = GorbowTermPrefixCode.encode (shiftTerm b t)

def ExactRejection : Prop :=
  ∀ n b raw, shiftCode n b raw = none ↔ GorbowTermPrefixCode.decode n raw = none

def ActualSemantics : Prop :=
  ∀ (n b : Nat) (t : Term n) (I : Interpretation) (v : Fin (n+b) → Nat),
    (shiftTerm b t).realize I v = t.realize I (fun i => v (shiftVar n b i))

def UniformPrograms : Prop :=
  Primrec (fun p : Nat × State × Nat => shiftedToken p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × OutputState × Nat => shiftStep p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => shiftRaw p.1 p.2.1 p.2.2) ∧
  Primrec (fun p : Nat × Nat × List Nat => shiftCode p.1 p.2.1 p.2.2)

def Target : Prop := ScannerInvariant ∧ ExactOutput ∧ ExactRejection ∧ ActualSemantics ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowTermShiftCode
