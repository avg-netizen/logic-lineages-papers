module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.Definitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.Targets
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowTheoryProof List.Vector SixSol20261113
/-- Exact original encoding, including arbitrary invalid raw streams. -/
def NativeLine : Prop := ∀ left right fixed : List Nat,
 evaluate lineConstructor (Encodable.encode left ::ᵥ Encodable.encode right ::ᵥ Encodable.encode fixed ::ᵥ nil) =
  Encodable.encode (nativeLine left right fixed)
/-- All-input calibration, preserving the original logical function and fallback. -/
def NativeRefinement : Prop := ∀ old : Program 1,
 (∀ v, evaluate old v = HistoryDispatcher.logicalFunction v) →
 ∀ v, evaluate (logicalLeaf old) v = HistoryDispatcher.logicalFunction v
/-- Symbolic three-input constructor equation, without a validity assumption. -/
def InternalLine : Prop := ∀ n (p : Program n) (qtag ptag ctag atag : Nat),
 (nodes p)[qtag]? = some ⟨3,lineConstructor⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 ∀ ctx (left right fixed : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.equal (lineCall qtag left right fixed) (lineValue ptag ctag atag left right fixed)))
/-- Actual reconstructed-candidate test, not an assumed recognizer success.
Search occurrence, bounded internal logical acceptance and original formula
validity/dispatcher/source installation remain separate later obligations. -/
def InternalTest : Prop := ∀ n (p : Program n)
 (qtag testTag ptag ctag atag vtag : Nat),
 (nodes p)[qtag]? = some ⟨3,lineConstructor⟩ →
 (nodes p)[testTag]? = some ⟨2,candidateTest⟩ →
 (nodes p)[ptag]? = some ⟨2,HistoryCodec.pair⟩ →
 (nodes p)[ctag]? = some ⟨2,HistoryCodec.cons⟩ →
 (nodes p)[atag]? = some ⟨2,HistoryAppend.append⟩ →
 (nodes p)[vtag]? = some ⟨1,TwoSol20261113.ReflexivityRecognizer.termValidator⟩ →
 ∀ ctx (left right fixed : Term ctx), Nonempty (Derivation (GorbowPRNumeralCalculation.Theory p)
  (.imp (RawReflexivityDispatcher.valid vtag left)
   (.imp (RawReflexivityDispatcher.valid vtag right)
    (.imp (RawReflexivityDispatcher.valid vtag fixed)
     (.equal (RawSuffixSearch.testCall testTag fixed (lineCall qtag left right fixed)) (.succ .zero))))))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace.Targets
