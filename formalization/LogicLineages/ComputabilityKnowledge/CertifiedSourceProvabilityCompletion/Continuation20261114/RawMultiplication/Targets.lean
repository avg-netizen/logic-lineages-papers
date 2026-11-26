module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
def ZeroNativeLine : Prop := ∀ raw : List Nat,
 evaluate Zero.lineConstructor (Encodable.encode raw ::ᵥ nil) = Encodable.encode (Zero.nativeLine raw)
def ZeroInternalLine : Prop := ∀ n (p : Program n) (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨1,Zero.lineConstructor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (Zero.lineCall qtag raw) (Zero.lineValue ptag ctag atag raw)))
def ZeroInternalArithmetic : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨1,Zero.lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,arithmeticLeaf old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (raw : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag raw)
   (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (Zero.lineCall qtag raw)) (.succ .zero))))
def SuccNativeLine : Prop := ∀ left right : List Nat,
 evaluate Succ.lineConstructor (Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ nil) =
  Encodable.encode (Succ.nativeLine left right)
def SuccInternalLine : Prop := ∀ n (p : Program n) (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨2,Succ.lineConstructor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (left right : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (Succ.lineCall qtag left right) (Succ.lineValue ptag ctag atag left right)))
def SuccInternalArithmetic : Prop := ∀ n (p : Program n) (old : Program 1)
 (qtag ltag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨2,Succ.lineConstructor⟩ →
 (nodes p)[ltag]? = some ⟨1,arithmeticLeaf old⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (left right : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag left)
   (.imp (RawReflexivityDispatcher.valid vtag right)
    (.equal (TwoSol20261113.ReflexivityRecognizer.leafCall ltag (Succ.lineCall qtag left right)) (.succ .zero)))))
def NativeRefinement : Prop := ∀ old : Program 1,
 (∀ v, evaluate old v = HistoryDispatcher.arithmeticFunction v) →
 ∀ v, evaluate (arithmeticLeaf old) v = HistoryDispatcher.arithmeticFunction v
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication.Targets
