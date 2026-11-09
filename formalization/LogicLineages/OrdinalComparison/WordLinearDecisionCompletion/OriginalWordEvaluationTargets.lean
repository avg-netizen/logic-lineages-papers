module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Targets
open PolynomialGraphCompletion

/-- Calibration is total, including malformed letters; source meaning still
requires the original domain. No companion/tail restriction is assumed. -/
def LetterCorrect : Prop := ∀ a : Letter, ∀ t : Nat, letter a t = letterValue a t

def LetterDomainCorrect : Prop := ∀ a : Letter, ∀ t : Nat,
  letterDomain a t = true ↔ LetterDomain a t

def WordCorrect : Prop := ∀ w : Word, ∀ t : Nat, word w t = wordValue w t

def WordDomainCorrect : Prop := ∀ w : Word, ∀ t : Nat,
  wordDomain w t = true ↔ WordDomain w t

def LetterPrograms : Prop :=
  Computable (fun p : Letter × Nat => letter p.1 p.2) ∧
  Computable (fun p : Letter × Nat => letterDomain p.1 p.2)

def WordPrograms : Prop :=
  Computable (fun p : Word × Nat => word p.1 p.2) ∧
  Computable (fun p : Word × Nat => wordDomain p.1 p.2)

def RowSubstitution : Prop := ∀ x n : Nat, ∀ r : Row, ∀ ν : Nat → Nat,
  RowValue (specializeRow x n r) ν = RowValue r (Function.update ν x n)

def FormulaSubstitution : Prop := ∀ x n : Nat, ∀ p : Formula, ∀ ν : Nat → Nat,
  (Formula.eval ν (specialize x n p) ↔ Formula.eval (Function.update ν x n) p) ∧
  (Formula.meaningful p (Function.update ν x n) ↔
    removedDomains x n p = true ∧ Formula.meaningful (specialize x n p) ν)

/-- Exact surviving-token equality pays names/degree preservation and removes
the chosen raw name. No newly generated word can enter a prefix branch. -/
def ExactSupport : Prop := ∀ x n : Nat, ∀ p : Formula,
  Formula.tokens (specialize x n p) = p.tokens.filter (fun t => t.1 != x)

def LiteralCodeCalibration : Prop := ∀ x n : Nat, ∀ p : Formula,
  Code.specialize x n (Formula.encode p) = Formula.encode (specialize x n p) ∧
  Code.removedDomains x n (Formula.encode p) = removedDomains x n p

def NumericPrograms : Prop :=
  Computable (fun p : Nat × Nat × Row => specializeRow p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat => Code.specialize p.1 p.2.1 p.2.2) ∧
  Computable (fun p : Nat × Nat × Nat => Code.removedDomains p.1 p.2.1 p.2.2)

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Targets
