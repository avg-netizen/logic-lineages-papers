module
public import LogicLineages.StandardControlCurrent.PolynomialBoolean.Definitions

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolynomialBoolean.Targets
open OrdinalComparison PolynomialGraphCompletion

def LiteralCompiler : Prop :=
  ∀ (d : Nat) (p : Source), Code.package d (sourceCode p) =
    (p.degree,(compile d p).1,
      WordLinearDecisionCompletion.Formula.encode (matrix d p false),
      WordLinearDecisionCompletion.Formula.encode (matrix d p true))

def CompilerPrograms : Prop :=
  Computable (fun a : Nat × Nat => Code.package a.1 a.2) ∧
  Computable (fun a : Nat × Nat => Code.flags a.1 a.2)

/-- Actual fresh frame-preserving graph realization with correlated output. -/
def GlobalRealization : Prop := ∀ (d start : Nat) (p : Source), p.Valid d → d ≤ start →
  ∀ ρ : Nat → Nat, ∃ ν : Nat → Nat,
    (∀ i, i < start ∨ (compile start p).1 ≤ i → ν i = ρ i) ∧
    RowsHold (compile start p).2.1 ν ∧
    (WordLinearDecisionCompletion.Formula.eval ν (compile start p).2.2 ↔ p.eval ρ)

def GlobalSoundness : Prop := ∀ (d start : Nat) (p : Source), p.Valid d → d ≤ start →
  ∀ ν : Nat → Nat, RowsHold (compile start p).2.1 ν →
    (WordLinearDecisionCompletion.Formula.eval ν (compile start p).2.2 ↔ p.eval ν)

/-- Every word occurrence is in-domain even in negated/inactive branches. -/
def MatrixDomains : Prop := ∀ (d : Nat) (p : Source), p.Valid d →
  3 ≤ p.degree ∧ ∀ c : Bool,
    WordLinearDecisionCompletion.Formula.allowed p.degree (matrix d p c) ∧
    ∀ ν : Nat → Nat, WordLinearDecisionCompletion.Formula.meaningful (matrix d p c) ν

def ExistentialCalibration : Prop := ∀ (d : Nat) (p : Source), p.Valid d →
  ( (∃ ν : Nat → Nat, WordLinearDecisionCompletion.Formula.meaningful (matrix d p false) ν ∧
      WordLinearDecisionCompletion.Formula.eval ν (matrix d p false)) ↔
    ∃ ρ : Nat → Nat, Positive d ρ ∧ p.eval ρ ) ∧
  ( (∃ ν : Nat → Nat, WordLinearDecisionCompletion.Formula.meaningful (matrix d p true) ν ∧
      WordLinearDecisionCompletion.Formula.eval ν (matrix d p true)) ↔
    ∃ ρ : Nat → Nat, Positive d ρ ∧ ¬p.eval ρ )

/-- Full current18 polynomial Boolean comparison for arbitrary finite input
scope, literal source trees, both positive-input closures and actual flags. -/
def PolynomialBooleanComparison : Prop :=
  LiteralCompiler ∧ CompilerPrograms ∧ GlobalRealization ∧ GlobalSoundness ∧ MatrixDomains ∧
  ExistentialCalibration ∧
  ∀ (d : Nat) (p : Source), p.Valid d →
    ((Code.flags d (sourceCode p)).1 = true ↔ ∃ ρ : Nat → Nat, Positive d ρ ∧ p.eval ρ) ∧
    ((Code.flags d (sourceCode p)).2 = true ↔ ∀ ρ : Nat → Nat, Positive d ρ → p.eval ρ)

end LogicLineages.StandardControlCurrent.PolynomialBoolean.Targets
