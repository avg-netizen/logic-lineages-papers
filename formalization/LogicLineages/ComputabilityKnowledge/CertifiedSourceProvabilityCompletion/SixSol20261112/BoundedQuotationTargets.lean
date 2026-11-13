module

public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedMPTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedQuotationTargets
open GorbowSyntax GorbowPRProgram GorbowTheoryProof GorbowPublishedDCB

/-- Literal bounded quotation for the original source predicate. Certificate
is bound INSIDE the object formula; fuel and bound are fixed external naturals.
This is not the unbounded source HB3 statement. -/
def statement (pF : Program 1) (c : Code) (sigma : Sentence) (fuel bound : Nat) : Sentence :=
  SourceBaseCompletion.BoundedRange.bounded bound
    (.imp (BoundedMP.checkerAt pF c fuel
      (GorbowSortedSyntaxCode.formulaCode (.imp (rho pF c) sigma)) (.var 0))
      (weakenClosed 1 (prD pF c (prD pF c sigma))))

def BoundedSourceQuotation : Prop :=
  ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
  ∀ (sigma : Sentence) (fuel bound : Nat),
    Nonempty (Derivation (S pF pR q) (statement pF c sigma fuel bound))

end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261112.BoundedQuotationTargets
