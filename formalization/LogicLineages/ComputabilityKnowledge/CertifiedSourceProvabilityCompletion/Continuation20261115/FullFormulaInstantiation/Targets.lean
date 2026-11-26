module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.Targets
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations GorbowTheoryProof List.Vector SixSol20261113
/-- Native correspondence to the ORIGINAL allInstantiate axiom, closed substitution. -/
def NativeLine : Prop := ∀ (f : Formula 1) (u : Term 0),
 evaluate (line f) (Encodable.encode (GorbowTermPrefixCode.encode u) ::ᵥ nil) =
 Encodable.encode (nativeLine f u)
/-- Original checker acceptance, not a new recognizer; well-formed closed argument only. -/
def NativeAcceptance : Prop := ∀ (f : Formula 1) (u : Term 0),
 HistoryDispatcher.logicalFunction (Encodable.encode (nativeLine f u) ::ᵥ nil) = 1
/-- Literal constructor graph on every numeric raw input, without a validation premise.
Does not assert original checker acceptance on malformed arguments. -/
def InternalLine : Prop := ∀ (f : Formula 1) n (p : Program n) (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨1,line f⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.equal (call qtag (raw ::ᵥ nil)) (lineValue ptag ctag atag f raw)))
/-- All-input original logical-function calibration with unchanged fallback.
The template is fixed before the runtime input; this is not a universal AST evaluator. -/
def NativeRefinement : Prop := ∀ (f : Formula 1) (old : Program 1),
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
 ∀ v, evaluate (logicalLeaf f old) v = HistoryDispatcher.logicalFunction v
/-- Genuine internal implication for original rule0/tag13 [phi,u].
No native calibration is reflected into this derivation. -/
def InternalLogical : Prop := ∀ (f : Formula 1) n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨1,line f⟩ →
 (nodes p)[ltag]? = some ⟨1,logicalLeaf f old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
 (.imp (RawReflexivityDispatcher.valid vtag raw)
  (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (call qtag (raw ::ᵥ nil))) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.FullFormulaInstantiation.Targets
