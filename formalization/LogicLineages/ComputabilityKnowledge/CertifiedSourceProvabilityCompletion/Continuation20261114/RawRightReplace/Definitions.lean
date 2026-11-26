module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawIteratedSucc.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Original equality replacement with variable first: φ(x) = (x = v).
The template prefix is exactly [0,0,0] ++ v; no extra annotation slot. -/
def templateRaw {n : Nat} (v : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n 0)
  (applyTwo HistoryCodec.cons (constant n 0) (applyTwo HistoryCodec.cons (constant n 0) v))
def formulaRaw {n : Nat} (a b v : Program n) : Program n :=
 RawSuccReplace.binaryRaw 7 (RawSuccReplace.binaryRaw 0 a b)
  (RawSuccReplace.binaryRaw 7 (RawSuccReplace.binaryRaw 0 a v) (RawSuccReplace.binaryRaw 0 b v))
def line {n : Nat} (a b v : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (formulaRaw a b v)
   (applyTwo HistoryCodec.pair (constant n 0)
    (applyTwo HistoryCodec.pair (constant n 12)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons (templateRaw v)
       (applyTwo HistoryCodec.cons a (applyTwo HistoryCodec.cons b (constant n 0))))
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor : Program 3 := line (.projection 0) (.projection 1) (.projection 2)
def templateCode : Program 1 := applyOne HistoryLookup.head TwoSol20261113.ReflexivityRecognizer.argsCode
def fixedTermCode : Program 1 := applyOne HistoryLookup.tail
 (applyOne HistoryLookup.tail (applyOne HistoryLookup.tail templateCode))
def leftTermCode : Program 1 := RawSuccReplace.leftTermCode
def rightTermCode : Program 1 := RawSuccReplace.rightTermCode
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (line leftTermCode rightTermCode fixedTermCode))
 (conjunction (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator leftTermCode)
  (conjunction (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator rightTermCode)
   (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator fixedTermCode)))
def logicalLeaf (old : Program 1) : Program 1 := choose recognizer old (constant 1 1)
def nativeTemplate (v : List Nat) : List Nat := 0 :: 0 :: 0 :: v
def nativeFormula (a b v : List Nat) : List Nat :=
 GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 0 a b)
  (GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 0 a v) (GorbowCodeConstructors.binary 0 b v))
def nativeLine (a b v : List Nat) : GorbowProofChecker.Line :=
 (0,nativeFormula a b v,0,12,[nativeTemplate v,a,b],0,0)
def binaryValue {ctx : Nat} (ctag atag token : Nat) (a b : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral token) (HistoryAppend.appendCall atag a b)
def templateValue {ctx : Nat} (ctag : Nat) (v : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero (HistoryLookup.consCall ctag .zero (HistoryLookup.consCall ctag .zero v))
def formulaValue {ctx : Nat} (ctag atag : Nat) (a b v : Term ctx) : Term ctx :=
 binaryValue ctag atag 7 (binaryValue ctag atag 0 a b)
  (binaryValue ctag atag 7 (binaryValue ctag atag 0 a v) (binaryValue ctag atag 0 b v))
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (a b v : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (formulaValue ctag atag a b v)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 12)
     (HistoryKernel.pairCall ptag
      (HistoryLookup.consCall ctag (templateValue ctag v)
       (HistoryLookup.consCall ctag a (HistoryLookup.consCall ctag b .zero)))
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (a b v : Term ctx) : Term ctx := call tag (a ::ᵥ b ::ᵥ v ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawRightReplace
