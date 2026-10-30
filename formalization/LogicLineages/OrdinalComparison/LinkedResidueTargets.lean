module
public import LogicLineages.OrdinalComparison.LinkedResidueDefinitions

@[expose] public section

/-! Actual linked arithmetic from paper10 eq:delta and lem:residue/lem:bounds,
paper.tex372–378,534–591. The stronger domain u>=4 includes every original
Theta-entry u=Phi(v). No independently assumed exponential budget is used.
The real-exponential gap and all Cartier/residue identities are separate. -/

namespace LogicLineages.OrdinalComparison.Targets

def ActualLinkedBudgetExponent : Prop :=
  ∀ u : Nat,
    actualLinkedBudget u = 2 ^ actualLinkedBinaryExponent u ∧
    2 ^ (u + 100) ≤ actualLinkedBinaryExponent u

def ActualLinkedResidueArithmetic : Prop :=
  ∀ u : Nat, 4 ≤ u →
    96 ≤ actualLinkedHalfExponent u ∧
    actualLinkedDegree u < actualLinkedHalfExponent u ∧
    2 * actualLinkedOffset u < actualLinkedDegree u ∧
    0 < actualLinkedDegree u - 2 * actualLinkedOffset u ∧
    actualLinkedDegree u - 2 * actualLinkedOffset u < actualLinkedModulus u ∧
    actualLinkedModulus u = actualLinkedBudget u / 2 + 1 ∧
    u ≤ actualLinkedBudget u ∧
    actualLinkedModulus u ≤ actualLinkedCutoff u ∧
    actualLinkedCutoff u < 2 * actualLinkedModulus u ∧
    actualLinkedTail u < actualLinkedModulus u ∧
    actualLinkedCutoff u - actualLinkedModulus u =
      actualLinkedModulus u - 1 - actualLinkedTail u

end LogicLineages.OrdinalComparison.Targets
