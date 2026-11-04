module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecisionDefinitions
public import Mathlib.Computability.Primrec.List
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision.Targets

/-- Literal common source domain from ALL original occurrences, a strictly
valid computed tail witness, and actual whole-matrix tail truth. No arbitrary
entrywise valuations, supplied normalization theorem or extrema assumptions. -/
def OriginalDomainAndMatrixTail : Prop := ∀ M : Matrix,
  (∀ n : Nat, matrixDomain M ≤ n ↔
    ∀ C ∈ M, ∀ a ∈ C, ∀ occurrence ∈ a.1.1, 0 ≤ (n : Int) + occurrence.2) ∧
  matrixDomain M < matrixThreshold M ∧
  (∀ n : Nat, matrixThreshold M ≤ n → matrixValue M n = tailValue M)

/-- Genuine total existential decision for THIS entire unary finite-DNF
source family, on its exact original common signed-shift domain. Empty and
cancelled rows/clauses/matrices and every desired integer sign included. -/
def ActualExistentialDecision : Prop := ∀ M : Matrix,
  existsDecision M = true ↔ ∃ n : Nat, matrixDomain M ≤ n ∧ matrixValue M n = true

/-- Genuine total universal decision on the SAME common source domain. This
is not the arbitrary multi-variable Snyatkov theorem or an assumed solver. -/
def ActualUniversalDecision : Prop := ∀ M : Matrix,
  forallDecision M = true ↔ ∀ n : Nat, matrixDomain M ≤ n → matrixValue M n = true

/-- Executable uniform primitive-recursive data AND both actual decision
bits, with standard Nat/Int/list encoding and no source-effectivity premise. -/
def ActualPrimitiveRecursion : Prop :=
  Primrec matrixDomain ∧ Primrec matrixThreshold ∧ Primrec₂ matrixValue ∧
  Primrec tailValue ∧ Primrec existsDecision ∧ Primrec forallDecision

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision.Targets
