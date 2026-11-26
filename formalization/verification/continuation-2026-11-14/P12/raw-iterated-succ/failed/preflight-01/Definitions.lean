module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawComputationSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc
open GorbowSyntax GorbowPRProgram GorbowPRRegistry GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Actual unary state [leftRaw,rightRaw,certificate], encoded by original pair. -/
def leftRaw : Program 1 := applyOne (HistoryDecoder.decoder false) (.projection 0)
def rightRaw : Program 1 := applyOne (HistoryDecoder.decoder false)
 (applyOne (HistoryDecoder.decoder true) (.projection 0))
def inputCertificate : Program 1 := applyOne (HistoryDecoder.decoder true)
 (applyOne (HistoryDecoder.decoder true) (.projection 0))
def mp (result imp ant : Program 1) : Program 1 := .composition LiteralRawMP.constructor
 (Fin.cases (constant 1 0) (Fin.cases result (Fin.cases imp (Fin.cases ant Fin.elim0))))
def outputRaw : Program 1 := RawSuccReplace.binaryRaw 0
 (RawAddSucc.successorRaw leftRaw) (RawAddSucc.successorRaw rightRaw)
def selfRaw : Program 1 := RawSuccReplace.binaryRaw 0
 (RawAddSucc.successorRaw leftRaw) (RawAddSucc.successorRaw leftRaw)
def intermediateRaw : Program 1 := RawSuccReplace.binaryRaw 7 selfRaw outputRaw
def replacementCertificate : Program 1 := applyTwo HistoryCodec.cons
 (RawSuccReplace.line leftRaw rightRaw) (constant 1 0)
def reflexivityCertificate : Program 1 := applyTwo HistoryCodec.cons
 (TwoSol20261113.ReflexivityRecognizer.reflexiveLine (RawAddSucc.successorRaw leftRaw)) (constant 1 0)
def outputCertificate : Program 1 :=
 mp outputRaw (mp intermediateRaw replacementCertificate inputCertificate) reflexivityCertificate
def step : Program 1 := applyTwo HistoryCodec.pair (RawAddSucc.successorRaw leftRaw)
 (applyTwo HistoryCodec.pair (RawAddSucc.successorRaw rightRaw) outputCertificate)
/-- Original primitive recursion, inputs [count,initialState]; counter does not
replace or bound the original certificate code used by the verifier. -/
def iterator : Program 2 := .recursion (.projection 0)
 (applyOne step (.projection (1 : Fin 3)))
structure Installation {n : Nat} (p : Program n) (old a : Program 1) (x : Program 3) extends
 RawSuccCongruence.Installation p old a x where
 leftTag : Nat
 stepTag : Nat
 iteratorTag : Nat
 hleft : (nodes p)[leftTag]? = some ⟨1,HistoryDecoder.decoder false⟩
 hstep : (nodes p)[stepTag]? = some ⟨1,step⟩
 hiterator : (nodes p)[iteratorTag]? = some ⟨2,iterator⟩
def state {ctx : Nat} (ptag : Nat) (t u cert : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag t (HistoryKernel.pairCall ptag u cert)
def stepCall {ctx : Nat} (tag : Nat) (s : Term ctx) : Term ctx := call tag (s ::ᵥ nil)
def iteratorCall {ctx : Nat} (tag : Nat) (count s : Term ctx) : Term ctx := call tag (count ::ᵥ s ::ᵥ nil)
def first {ctx : Nat} (leftTag : Nat) (s : Term ctx) : Term ctx := call leftTag (s ::ᵥ nil)
def second {ctx : Nat} (leftTag rightTag : Nat) (s : Term ctx) : Term ctx :=
 call leftTag (call rightTag (s ::ᵥ nil) ::ᵥ nil)
def third {ctx : Nat} (rightTag : Nat) (s : Term ctx) : Term ctx :=
 call rightTag (call rightTag (s ::ᵥ nil) ::ᵥ nil)
def invariant {ctx : Nat} (vtag qctag ctag atag leftTag rightTag : Nat)
 (index fuel s : Term ctx) : Formula ctx :=
 .conj (RawReflexivityDispatcher.valid vtag (first leftTag s))
  (.conj (RawReflexivityDispatcher.valid vtag (second leftTag rightTag s))
   (.equal (LiteralCheckerAcceptance.coreCall qctag index fuel .zero
    (.add (RawSuccCongruence.inputRaw ctag atag (first leftTag s) (second leftTag rightTag s))
     (RawSuccCongruence.inputRaw ctag atag (first leftTag s) (second leftTag rightTag s)))
    (third rightTag s)) (.succ .zero)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc
