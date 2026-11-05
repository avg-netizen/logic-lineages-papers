module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsTargets
open NormalForm (Formula)
open PlainFrontierPrograms

def LiteralAdvance : Prop := ∀ s : PlainFrontier.State,
  Code.advance (encodeState s) = encodeState (PlainFrontier.advance s)

def LiteralIteration : Prop := ∀ (n : Nat) (s : PlainFrontier.State),
  Code.run n (encodeState s) = encodeState (PlainFrontier.run n s)

def LiteralDecisionData : Prop := ∀ p : Formula,
  Code.fuel p.encode = PlainFrontier.fuel p ∧
  Code.initial p.encode = encodeState (PlainFrontier.initial p) ∧
  Code.answer p.encode = PlainFrontier.answer p ∧
  Code.decide p.encode = PlainFrontier.decide p

def ActualNumericPrograms : Prop :=
  Primrec Code.advance ∧ Primrec₂ Code.run ∧ Primrec Code.fuel ∧
    Primrec Code.initial ∧ Primrec Code.answer ∧ Primrec Code.decide

def ActualEncodedDecision : Prop := ∀ p : Formula, MaximalPlainBranch.isPlain p = true → ∀ b : Bool,
  Code.decide p.encode = some b ↔ (PlainLinearCleanup.Satisfiable p ↔ b = true)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainFrontierProgramsTargets
