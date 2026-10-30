module

public import LogicLineages.ComputabilityKnowledge.OraclePiTwoDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OraclePiTwoTargets
open OracleJump OraclePiTwo

def OrdinaryWitnessCompiler : Prop :=
  ∀ matrix : Nat × Nat × Nat → Bool, Primrec matrix →
    ∃ code : Nat.Partrec.Code, (∀ query, code.eval query = witnessSearch matrix query) ∧
      WitnessCompilerSemantics matrix code

def RelativeCounterSearch : Prop :=
  ∀ code : Nat.Partrec.Code,
    RecursiveIn {fun n => Part.some (firstJump n)} (counterSearch code)

def ExactCounterSearchDomain : Prop :=
  ∀ (matrix : Nat × Nat × Nat → Bool) (code : Nat.Partrec.Code), WitnessCompilerSemantics matrix code →
    ∀ i, (counterSearch code i).Dom ↔ ∃ x, ∀ y, matrix (i, x, y) = false

def ActualPiTwoSecondJumpDecision : Prop :=
  ∀ matrix : Nat × Nat × Nat → Bool, Primrec matrix →
    ComputableIn {fun n => Part.some (secondJump n)} (matrixIndicator matrix)

end LogicLineages.ComputabilityKnowledge.OraclePiTwoTargets
