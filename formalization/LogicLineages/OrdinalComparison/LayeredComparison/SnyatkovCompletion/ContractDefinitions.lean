module
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseFormulaDefinitions
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovInverseDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion
open CommonLayerSyntax

/-- Arbitrary first-order source BASE syntax. Variable names retain their
original identities; quantifiers bind one name with ordinary shadowing. -/
inductive SourceFormula where
  | equal (left right : BaseTerm)
  | less (left right : BaseTerm)
  | negative (body : SourceFormula)
  | conjunction (left right : SourceFormula)
  | existsNat (name : Nat) (body : SourceFormula)

def SourceFormula.eval (ν : Nat → Nat) : SourceFormula → Prop
  | .equal a b => a.value ν = b.value ν
  | .less a b => a.value ν < b.value ν
  | .negative p => ¬p.eval ν
  | .conjunction p q => p.eval ν ∧ q.eval ν
  | .existsNat i p => ∃ n : Nat, p.eval (Function.update ν i n)

def SourceFormula.variables : SourceFormula → List Nat
  | .equal a b | .less a b => a.variables ++ b.variables
  | .negative p => p.variables
  | .conjunction p q => p.variables ++ q.variables
  | .existsNat i p => p.variables.filter (fun j => j != i)

def SourceFormula.encode : SourceFormula → Nat
  | .equal a b => 5 * Nat.pair a.encode b.encode
  | .less a b => 5 * Nat.pair a.encode b.encode + 1
  | .negative p => 5 * p.encode + 2
  | .conjunction p q => 5 * Nat.pair p.encode q.encode + 3
  | .existsNat i p => 5 * Nat.pair i p.encode + 4

/-- Explicit total expanded terms used in Snyatkov's pp40--51 elimination.
Subtraction is natural truncated subtraction, including below-range defaults.
Every auxiliary has its displayed actual arithmetic semantics; the final
decision needs proved numeric computation and calibration of this output.
No auxiliary is an assumed semantic supplier. -/
inductive Term where
  | numeral (n : Nat)
  | variable (i : Nat)
  | add (left right : Term)
  | subtract (left right : Term)
  | multiply (coefficient : Nat) (input : Term)
  | divide (divisor : Nat) (input : Term)
  | phi (input : Term)
  | hyper (input : Term)
  | phiInverse (input : Term)
  | hyperInverse (input : Term)

def Term.value (ν : Nat → Nat) : Term → Nat
  | .numeral n => n
  | .variable i => ν i
  | .add a b => a.value ν + b.value ν
  | .subtract a b => a.value ν - b.value ν
  | .multiply c a => c * a.value ν
  | .divide c a => a.value ν / c
  | .phi a => Phi (a.value ν)
  | .hyper a => FixedSeedControlResidue.H (a.value ν)
  | .phiInverse a => SnyatkovInverse.phiInverse (a.value ν)
  | .hyperInverse a => SnyatkovInverse.hyperInverse (a.value ν)

def Term.variables : Term → List Nat
  | .numeral _ => []
  | .variable i => [i]
  | .add a b | .subtract a b => a.variables ++ b.variables
  | .multiply _ a | .divide _ a | .phi a | .hyper a |
      .phiInverse a | .hyperInverse a => a.variables

def Term.encode : Term → Nat
  | .numeral n => 10 * n
  | .variable i => 10 * i + 1
  | .add a b => 10 * Nat.pair a.encode b.encode + 2
  | .subtract a b => 10 * Nat.pair a.encode b.encode + 3
  | .multiply c a => 10 * Nat.pair c a.encode + 4
  | .divide c a => 10 * Nat.pair c a.encode + 5
  | .phi a => 10 * a.encode + 6
  | .hyper a => 10 * a.encode + 7
  | .phiInverse a => 10 * a.encode + 8
  | .hyperInverse a => 10 * a.encode + 9

/-- Quantifier-free expanded matrices, with one shared valuation across all
operands. Divisibility at zero is total arithmetic data, not a valid positive
modulus assertion in a source normalization theorem. -/
inductive Matrix where
  | truth | falsity
  | equal (left right : Term)
  | less (left right : Term)
  | divisible (modulus : Nat) (input : Term)
  | negative (body : Matrix)
  | conjunction (left right : Matrix)
  | disjunction (left right : Matrix)

def Matrix.eval (ν : Nat → Nat) : Matrix → Prop
  | .truth => True
  | .falsity => False
  | .equal a b => a.value ν = b.value ν
  | .less a b => a.value ν < b.value ν
  | .divisible m a => m ∣ a.value ν
  | .negative p => ¬p.eval ν
  | .conjunction p q => p.eval ν ∧ q.eval ν
  | .disjunction p q => p.eval ν ∨ q.eval ν

def Matrix.variables : Matrix → List Nat
  | .truth | .falsity => []
  | .equal a b | .less a b => a.variables ++ b.variables
  | .divisible _ a => a.variables
  | .negative p => p.variables
  | .conjunction p q | .disjunction p q => p.variables ++ q.variables

def Matrix.encode : Matrix → Nat
  | .truth => 0
  | .falsity => 1
  | .equal a b => 8 * Nat.pair a.encode b.encode + 2
  | .less a b => 8 * Nat.pair a.encode b.encode + 3
  | .divisible m a => 8 * Nat.pair m a.encode + 4
  | .negative p => 8 * p.encode + 5
  | .conjunction p q => 8 * Nat.pair p.encode q.encode + 6
  | .disjunction p q => 8 * Nat.pair p.encode q.encode + 7

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion
