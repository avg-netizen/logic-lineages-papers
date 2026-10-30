module

public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluation

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticEvaluation
open GorbowSyntax GorbowStandardInstances GorbowSortedSyntaxCode
open LogicLineages.ComputabilityKnowledge.GorbowArithmeticEvaluation

def StackCalibration : Prop := ∀ (t : Term 0), ArithmeticTerm t → ∀ I stack,
  run (GorbowTermPrefixCode.encode t) stack = some (t.realize I Fin.elim0 :: stack)

def ExactRawOutput : Prop := ∀ raw value I,
  rawValue raw=some value ↔ ∃ t : Term 0,
    raw=GorbowTermPrefixCode.encode t ∧ ArithmeticTerm t ∧ value=t.realize I Fin.elim0

def ExactSortedOutput : Prop := ∀ code value I,
  sortedValue code=some value ↔ ∃ t : Term 0,
    code=termCode t ∧ ArithmeticTerm t ∧ value=t.realize I Fin.elim0

def ExactRejection : Prop :=
  (∀ raw, rawValue raw=none ↔ GorbowClosedTermCode.arithmeticRaw raw=false) ∧
  (∀ code, sortedValue code=none ↔ GorbowSortedBooleanCode.arithmeticTermCode code=false)

def NumeralCalibration : Prop := ∀ n,
  sortedValue (termCode (Term.numeral n : Term 0))=some n

def UniformPrograms : Prop :=
  Primrec (fun p : Option (List Nat) × Nat => step p.1 p.2) ∧
  Primrec (fun p : List Nat × List Nat => run p.1 p.2) ∧
  Primrec rawValue ∧ Primrec sortedValue

def Target : Prop := StackCalibration ∧ ExactRawOutput ∧ ExactSortedOutput ∧
  ExactRejection ∧ NumeralCalibration ∧ UniformPrograms
end LogicLineages.ComputabilityKnowledge.Comparators.GorbowArithmeticEvaluation
