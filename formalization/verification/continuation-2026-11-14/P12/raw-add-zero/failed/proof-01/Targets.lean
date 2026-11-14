module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
/-- Exact original line encoding for all raw streams; construction needs no validity. -/
def NativeLine : Prop := ∀ raw : List Nat,
 evaluate lineConstructor (Encodable.encode raw ::ᵥ nil) = Encodable.encode (nativeLine raw)
/-- All-natural-input calibration to the ORIGINAL arithmeticFunction, including
malformed inputs and every unchanged fallback case. This is not an internal premise. -/
def NativeRefinement : Prop := ∀ old : Program 1,
 (∀ v, evaluate old v = HistoryDispatcher.arithmeticFunction v) →
 ∀ v, evaluate (arithmeticLeaf old) v = HistoryDispatcher.arithmeticFunction v
/-- Independent symbolic equation for the actual uniform add-zero constructor. -/
def InternalLine : Prop := ∀ n (p : Program n) (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨1,lineConstructor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall qtag raw) (lineValue ptag ctag atag raw)))
/-- Genuine internal arithmetic-axiom acceptance from actual raw term validity.
The conclusion concerns t+0=t (rule1/tag2), not t=t or a native evaluator.
Dispatcher/CORE/source integration and general computation/HB3 remain separate. -/
def InternalArithmetic : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨1,lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,arithmeticLeaf old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (lineCall qtag raw)) (.succ .zero))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero.Targets
