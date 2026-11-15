module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourLeaf.StatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPublishedDCB GorbowTheoryProof SixSol20261113
open FiniteRuleFourLeaf
/-- Literal rule4 acceptance through the original dispatcher, at the already
chosen root. Neither leaf success nor validator success is a premise. -/
def FiniteLiteralDispatcher : Prop :=
 ∀ (pF pR : Program 1) (q : Program 5) (c : Code), Actual pF pR q c →
 ∀ (logical arithmetic : Program 1) (x : Program 3) (xtag dtag : Nat),
 (∀ v, evaluate x v = HistoryDispatcher.axiomFunction v) →
 (nodes (sourceRoot pF pR q))[xtag]? = some ⟨3,SaturatedAxiomLeaf.saturated x⟩ →
 (nodes (sourceRoot pF pR q))[dtag]? = some ⟨4,
  HistoryDispatcher.lineDispatcher LiteralSyntaxValidator.lineValidator logical arithmetic
   (SaturatedAxiomLeaf.saturated x)⟩ →
 ∃ fuel : Nat, ∀ sigma : Sentence,
 sigma ∈ GorbowPRDefiningEquations.axioms (sourceRoot pF pR q) →
 ∀ ctx (larger history : Term ctx), Nonempty (Derivation (S pF pR q)
  (.imp (SixSol20261112.Fuel.orderGuard (Term.numeral fuel) larger)
   (.equal (HistoryDispatcher.dispatcherCall dtag (Term.numeral (Encodable.encode c))
    larger history (Term.numeral (lineCode sigma))) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FiniteRuleFourDispatcher.Targets
