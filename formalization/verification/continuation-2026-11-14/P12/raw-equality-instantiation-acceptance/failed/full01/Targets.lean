module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
/-- All-input original logical-function calibration with unchanged fallback.
The template is fixed before the runtime input; this is not a universal AST evaluator. -/
def NativeRefinement : Prop := ∀ (a b : Term 1) (old : Program 1),
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
 ∀ v, evaluate (logicalLeaf a b old) v = HistoryDispatcher.logicalFunction v
/-- Genuine internal implication for original rule0/tag13 [phi,u].
No native calibration is reflected into this derivation. -/
def InternalLogical : Prop := ∀ (a b : Term 1) n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨1,RawEqualityInstantiation.line a b⟩ →
 (nodes p)[ltag]? = some ⟨1,logicalLeaf a b old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid vtag raw)
  (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (call qtag (raw ::ᵥ nil))) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawEqualityInstantiationAcceptance.Targets
