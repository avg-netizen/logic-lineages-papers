module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.RelationalSyntaxDepthTransport.ClosedScanStatementChecks
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.Targets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthTargets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof
open SixSol20261113
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
/-- The actual original term-task singleton at an arbitrary internal binder bound. -/
def tasks {ctx : Nat} (ptag ctag : Nat) (bound : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (LiteralSyntaxStep.taskCall ptag 0 bound) .zero
/-- Original closed runtime term acceptance lifts to EVERY internal binder bound.
The premise is the actual installed closed-term validator; no decoded syntax,
closed native term witness, or scanner-success transfer is assumed. -/
def InternalClosedTermAtAnyDepth : Prop := ∀ n (p : Program n) (vtag stag ptag ctag atag : Nat),
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 (nodes p)[stag]? = some ⟨2,LiteralSyntaxScan.scanCode⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (bound raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.equal (LiteralSyntaxScan.scanCall stag (tasks ptag ctag bound) raw) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiationValidity.ClosedTermDepthTargets
