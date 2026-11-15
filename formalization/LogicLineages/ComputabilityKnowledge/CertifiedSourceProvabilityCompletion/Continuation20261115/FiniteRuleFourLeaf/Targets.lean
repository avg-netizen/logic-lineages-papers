module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
/-- Finite closed rule-4 seed at an already selected source, plus genuinely
internal symbolic-fuel transport. Calibration is an external equality of the
actual base program, not an internal axiom. No new source or success premise. -/
def FiniteLiteralLeaf : Prop :=
 ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
 ∀ (x : Program 3) (tag : Nat),
 (∀ v, evaluate x v = HistoryDispatcher.axiomFunction v) →
 (nodes (sourceRoot pF pR q))[tag]? = some ⟨3,SaturatedAxiomLeaf.saturated x⟩ →
 ∃ fuel : Nat, ∀ sigma : Sentence, sigma ∈ GorbowPRDefiningEquations.axioms (sourceRoot pF pR q) →
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory (sourceRoot pF pR q))
  (graphEquation tag x c fuel sigma)) ∧
 Nonempty (Derivation (GorbowPRNumeralCalculation.Theory (sourceRoot pF pR q))
  (SaturatedAxiomLeaf.success (ctx := 0) tag (Term.numeral (Encodable.encode c))
   (Term.numeral fuel) (Term.numeral (lineCode sigma)))) ∧
 (∀ ctx (larger : Term ctx), Nonempty (Derivation (S pF pR q)
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger)
   (SaturatedAxiomLeaf.success tag (Term.numeral (Encodable.encode c))
    larger (Term.numeral (lineCode sigma))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.Targets
