module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearDefinitions
public import Mathlib.Computability.Partrec

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearTargets
open NormalForm SourceRows

def ExactFreeLinearityTest : Prop := ∀ (i : Nat) (p : QFormula),
  QuantifiedLinear.freeLinear i p = true ↔
    ∀ s ∈ QuantifiedLinear.occurrences p, s.name = i → s = Summand.variable i

def ExactOutputOccurrences : Prop := ∀ (p : QFormula) (s : Summand),
  s ∈ LinearBlock.occurrences (QuantifiedLinear.eliminate p) ↔
    s ∈ QuantifiedLinear.occurrences p

def ExactOutputLinearity : Prop := ∀ (p : QFormula) (i : Nat),
  LinearRows.isLinear i (QuantifiedLinear.eliminate p) = QuantifiedLinear.freeLinear i p

def ActualQuantifierElimination : Prop := ∀ (p : QFormula),
  QuantifiedLinear.admissible p = true → ∀ ν : Nat → Nat,
    (QuantifiedLinear.eliminate p).eval ν ↔ p.eval ν

def ExactFreeVariableSupport : Prop := ∀ (p : QFormula) (i : Nat),
  i ∈ (QuantifiedLinear.eliminate p).variables ↔ i ∈ p.variables

def ExistingBlockCompatibility : Prop :=
  (∀ (names : List Nat) (p : Formula),
    QuantifiedLinear.admissible (bindAll names (.matrix p)) = LinearBlock.allLinear names p) ∧
  (∀ (names : List Nat) (p : Formula),
    QuantifiedLinear.eliminate (bindAll names (.matrix p)) = LinearBlock.eliminate names p)

def LiteralCodeCalibration : Prop :=
  (∀ (i : Nat) (p : QFormula),
    QuantifiedLinear.Code.freeLinear i p.encode = QuantifiedLinear.freeLinear i p) ∧
  (∀ p : QFormula,
    QuantifiedLinear.Code.admissible p.encode = QuantifiedLinear.admissible p) ∧
  (∀ p : QFormula,
    QuantifiedLinear.Code.eliminate p.encode = (QuantifiedLinear.eliminate p).encode)

def ActualNumericPrograms : Prop :=
  Primrec₂ QuantifiedLinear.Code.freeLinear ∧
  Primrec QuantifiedLinear.Code.admissible ∧ Primrec QuantifiedLinear.Code.eliminate

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.QuantifiedLinearTargets
