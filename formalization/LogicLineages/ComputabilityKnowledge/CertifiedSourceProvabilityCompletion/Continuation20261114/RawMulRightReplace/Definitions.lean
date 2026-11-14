module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuffixOccurrence.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Original tag12 template φ(x) = ((a*v)=(x*v)); v is a genuine
suffix of the original template, never a fourth annotation field. -/
def variableRaw (n : Nat) : Program n := applyTwo HistoryCodec.cons (constant n 0)
 (applyTwo HistoryCodec.cons (constant n 0) (constant n 0))
def templateRaw {n : Nat} (a v : Program n) : Program n :=
 RawSuccReplace.binaryRaw 0 (RawSuccReplace.binaryRaw 4 a v)
  (RawSuccReplace.binaryRaw 4 (variableRaw n) v)
def formulaRaw {n : Nat} (a b v : Program n) : Program n :=
 RawSuccReplace.binaryRaw 7 (RawSuccReplace.binaryRaw 0 a b)
  (RawSuccReplace.binaryRaw 7
   (RawSuccReplace.binaryRaw 0 (RawSuccReplace.binaryRaw 4 a v) (RawSuccReplace.binaryRaw 4 a v))
   (RawSuccReplace.binaryRaw 0 (RawSuccReplace.binaryRaw 4 a v) (RawSuccReplace.binaryRaw 4 b v)))
def line {n : Nat} (a b v : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (formulaRaw a b v)
   (applyTwo HistoryCodec.pair (constant n 0)
    (applyTwo HistoryCodec.pair (constant n 12)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons (templateRaw a v)
       (applyTwo HistoryCodec.cons a (applyTwo HistoryCodec.cons b (constant n 0))))
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor : Program 3 := line (.projection 0) (.projection 1) (.projection 2)
def templateCode : Program 1 := applyOne HistoryLookup.head TwoSol20261113.ReflexivityRecognizer.argsCode
def leftTermCode : Program 1 := RawSuccReplace.leftTermCode
def rightTermCode : Program 1 := RawSuccReplace.rightTermCode
/-- Inputs [candidateSuffix, originalLine]. Full reconstruction plus all three
original term validators. Candidate supplied only by literal bounded tail search. -/
def candidateTest : Program 2 :=
 let original : Program 2 := .projection 1
 let a := applyOne leftTermCode original
 let b := applyOne rightTermCode original
 let v : Program 2 := .projection 0
 conjunction (applyTwo equalCode original (line a b v))
  (conjunction (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator a)
   (conjunction (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator b)
    (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator v)))
def searchArguments : Fin 3 → Program 1 :=
 Fin.cases (.composition .succ (fun _ => applyOne HistoryLengthOffset.lengthProgram templateCode))
  (Fin.cases templateCode (Fin.cases (.projection 0) Fin.elim0))
def recognizer : Program 1 := .composition (RawSuffixSearch.search candidateTest) searchArguments
def logicalLeaf (old : Program 1) : Program 1 := choose recognizer old (constant 1 1)
def nativeTemplate (a v : List Nat) : List Nat :=
 GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.binary 4 a v)
  (GorbowCodeConstructors.binary 4 [0,0] v)
def nativeFormula (a b v : List Nat) : List Nat :=
 GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 0 a b)
  (GorbowCodeConstructors.binary 7
   (GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.binary 4 a v) (GorbowCodeConstructors.binary 4 a v))
   (GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.binary 4 a v) (GorbowCodeConstructors.binary 4 b v)))
def nativeLine (a b v : List Nat) : GorbowProofChecker.Line :=
 (0,nativeFormula a b v,0,12,[nativeTemplate a v,a,b],0,0)
def binaryValue {ctx : Nat} (ctag atag token : Nat) (a b : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral token) (HistoryAppend.appendCall atag a b)
def templateValue {ctx : Nat} (ctag atag : Nat) (a v : Term ctx) : Term ctx :=
 binaryValue ctag atag 0 (binaryValue ctag atag 4 a v)
  (binaryValue ctag atag 4 (HistoryLookup.consCall ctag .zero (HistoryLookup.consCall ctag .zero .zero)) v)
def formulaValue {ctx : Nat} (ctag atag : Nat) (a b v : Term ctx) : Term ctx :=
 binaryValue ctag atag 7 (binaryValue ctag atag 0 a b)
  (binaryValue ctag atag 7
   (binaryValue ctag atag 0 (binaryValue ctag atag 4 a v) (binaryValue ctag atag 4 a v))
   (binaryValue ctag atag 0 (binaryValue ctag atag 4 a v) (binaryValue ctag atag 4 b v)))
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (a b v : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (formulaValue ctag atag a b v)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 12)
     (HistoryKernel.pairCall ptag
      (HistoryLookup.consCall ctag (templateValue ctag atag a v)
       (HistoryLookup.consCall ctag a (HistoryLookup.consCall ctag b .zero)))
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (a b v : Term ctx) : Term ctx := call tag (a ::ᵥ b ::ᵥ v ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMulRightReplace
