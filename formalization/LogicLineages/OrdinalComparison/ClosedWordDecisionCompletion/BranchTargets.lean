module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchTargets
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion

/-- The Boolean congruence adapter preserves literal raw support and proves
raw-linearity for every possible maximum, without a residue oracle. -/
def ExactResidueSyntax : Prop := ∀ D (p : Formula),
  Formula.variables (residue p) = p.variables ∧
  (Formula.allowed D p → Formula.allowed D (residue p)) ∧
  ∀ maximum, OutcomeTransport.CongruencesLinear maximum (residue p)

def ExactResidueSemantics : Prop := ∀ D (p : Formula), Formula.allowed D p →
  ∀ ν : Nat → Nat, (∀ i ∈ p.variables,
    max (OutcomeTransport.originalTail p) (residueTail p) ≤ ν i) →
      Formula.meaningful p ν ∧ Formula.meaningful (residue p) ν ∧
      (Formula.eval ν (residue p) ↔ Formula.eval ν p)

/-- No branch loses the inherited introduction floor or adds an original
name. The deleted name really occurs, so deduplicated support decreases. -/
def ActualChildSyntax : Prop := ∀ D floor (p : Formula),
  3 ≤ D → Formula.allowed D p → ∀ b ∈ children D floor p,
    floor ≤ b.1 ∧ Formula.allowed D b.2 ∧
    (∃ x ∈ names p, ∀ i ∈ b.2.variables, i ≠ x ∧ i ∈ p.variables) ∧
    (names b.2).length < (names p).length

/-- Complete existential alternatives for the ORIGINAL current matrix,
including every explicit domain under every Boolean constructor. -/
def ActualChildEquivalence : Prop := ∀ D floor (p : Formula),
  3 ≤ D → Formula.allowed D p → names p ≠ [] →
    (SatisfiableAt floor p ↔ ∃ b ∈ children D floor p, SatisfiableAt b.1 b.2)

/-- Literal radix-six code calibration for the concrete compiled children. -/
def LiteralCodeCalibration : Prop :=
  (∀ p : Formula, Code.variables (Formula.encode p) = p.variables ∧
    Code.names (Formula.encode p) = names p ∧
    Code.residue (Formula.encode p) = Formula.encode (residue p) ∧
    Code.residueTail (Formula.encode p) = residueTail p) ∧
  (∀ D floor (p : Formula), Code.commonTail D floor (Formula.encode p) =
    commonTail D floor p) ∧
  (∀ D floor (p : Formula), Code.children D floor (Formula.encode p) =
    (children D floor p).map (fun b => (b.1,Formula.encode b.2)))

/-- Each input, including the degree, inherited floor and formula code, is
runtime data. No stage, row solver, domain or branch oracle is supplied. -/
def ActualNumericPrograms : Prop :=
  Primrec Code.variables ∧ Primrec Code.names ∧ Primrec Code.residue ∧
  Primrec Code.residueTail ∧
  Computable (fun input : Nat × Nat × Nat =>
    Code.commonTail input.1 input.2.1 input.2.2) ∧
  Computable (fun input : Nat × Nat × Nat =>
    Code.children input.1 input.2.1 input.2.2)

def FullBranchAssembly : Prop := ExactResidueSyntax ∧ ExactResidueSemantics ∧
  ActualChildSyntax ∧ ActualChildEquivalence ∧ LiteralCodeCalibration ∧ ActualNumericPrograms

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.BranchTargets
