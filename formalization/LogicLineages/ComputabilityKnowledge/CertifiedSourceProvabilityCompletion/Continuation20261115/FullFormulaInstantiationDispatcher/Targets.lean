module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- Actual original rule0/tag13 full-formula line, at arbitrary raw input and
index/fuel/history including zero. Only actual closed-term validity is assumed;
logical, formula, line-validator and dispatcher success must all be derived.
Installation supplies literal same-p AST memberships only, not acceptance. -/
def InternalDispatcher : Prop := ∀ (f : Formula 1) n (p : Program n)
 (old arithmetic : Program 1) (x : Program 3) (I : Installation p f old arithmetic x),
 ∀ ctx (raw index fuel history : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid I.vtag raw)
  (.equal (HistoryDispatcher.dispatcherCall I.dtag index fuel history
   (call I.qtag (raw ::ᵥ nil))) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationDispatcher.Targets
