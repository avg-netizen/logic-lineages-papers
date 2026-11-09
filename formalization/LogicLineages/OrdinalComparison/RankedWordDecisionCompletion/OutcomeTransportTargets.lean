module
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportTargets
open PolynomialGraphCompletion WordLinearDecisionCompletion OutcomeTransport

/-- Exact transport uses the original occurrence-order relation, at one
shared valuation. A sign tag never supplies a divisibility conclusion. -/
def ExactCorrelatedBody : Prop :=
  (∀ (maximum : Nat) (p : Formula) (outcomes : List Outcome) (ν : Nat → Nat),
    List.Forall₂ (fun r o => OutcomeCorrect maximum r o ν) (inequalityRows p) outcomes →
      (Formula.eval ν (OutcomeTransport.rewrite p outcomes) ↔ Formula.eval ν p)) ∧
  (∀ (p : Formula) (outcomes : List Outcome),
    congruences (OutcomeTransport.rewrite p outcomes) = congruences p)

/-- Body syntax/domain guarantees are unconditional on Boolean truth,
including false case guards. Congruences must explicitly be raw-linear in
the selected maximum; the separate residue compiler pays that condition. -/
def BodySyntaxAndDomains : Prop := ∀ (D maximum : Nat) (p : Formula) (outcomes : List Outcome),
  Formula.allowed D p → CongruencesLinear maximum p →
  outcomes.length = (inequalityRows p).length →
  (∀ o ∈ outcomes, RowAllowed D o.row ∧ NamesFrom p.variables o.row ∧
    (o.tag = 0 ∨ o.tag = 2 ∨ (o.tag = 3 ∧ LinearRow maximum o.row))) →
    Formula.allowed D (OutcomeTransport.rewrite p outcomes) ∧
    linear maximum (OutcomeTransport.rewrite p outcomes) = true ∧
    FormulaNamesFrom p.variables (OutcomeTransport.rewrite p outcomes) ∧
    ∀ ν, Formula.meaningful p ν → (∀ o ∈ outcomes, RowDomain o.row ν) →
      Formula.meaningful (OutcomeTransport.rewrite p outcomes) ν

/-- Exact literal numerical parsing and compilation, with repeated rows in
the original occurrence order and no semantic row-lookup oracle. -/
def LiteralCodeCalibration : Prop :=
  (∀ p : Formula, Code.inequalityRows (Formula.encode p) = inequalityRows p) ∧
  (∀ (p : Formula) (pack : Package),
    Code.transform (Formula.encode p) (encodePackage pack) = encodeMatrix (transform p pack)) ∧
  (∀ D maximum (p : Formula), Code.compile D maximum (Formula.encode p) =
    encodeMatrix (OutcomeTransport.compile D maximum p))

/-- Complete actual guarded matrix compiler, with the concrete row runner
bound internally. Every original/output domain is paid before case truth. -/
def ExactActualMatrix : Prop := ∀ D maximum (p : Formula),
  3 ≤ D → Formula.allowed D p → CongruencesLinear maximum p →
    MatrixCorrect D maximum p (OutcomeTransport.compile D maximum p)

/-- Uniform numeric source programs, including the bound actual row runner.
No Formula encodability instance, solver oracle or guard-consistency test is
substituted for the concrete radix-six compiler. -/
def ActualNumericPrograms : Prop :=
  Computable Code.inequalityRows ∧
  Computable (fun input : Nat × EncodedPackage => Code.transform input.1 input.2) ∧
  Computable (fun input : Nat × Nat × Nat => Code.compile input.1 input.2.1 input.2.2)

def FullOutcomeTransport : Prop :=
  ExactCorrelatedBody ∧ BodySyntaxAndDomains ∧ LiteralCodeCalibration ∧
    ExactActualMatrix ∧ ActualNumericPrograms

end LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportTargets
