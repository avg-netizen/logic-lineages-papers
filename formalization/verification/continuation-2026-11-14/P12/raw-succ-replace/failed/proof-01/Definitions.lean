module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawThreeSource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowInstanceCodeProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Original binary prefix syntax constructor. -/
def binaryRaw {n : Nat} (token : Nat) (a b : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n token) (applyTwo HistoryAppend.append a b)
def templateRaw {n : Nat} (a : Program n) : Program n :=
 binaryRaw 0 (RawAddSucc.successorRaw a)
  (RawAddSucc.successorRaw (applyTwo HistoryCodec.cons (constant n 0)
   (applyTwo HistoryCodec.cons (constant n 0) (constant n 0))))
def formulaRaw {n : Nat} (a b : Program n) : Program n :=
 binaryRaw 7 (binaryRaw 0 a b)
  (binaryRaw 7 (binaryRaw 0 (RawAddSucc.successorRaw a) (RawAddSucc.successorRaw a))
   (binaryRaw 0 (RawAddSucc.successorRaw a) (RawAddSucc.successorRaw b)))
/-- Original rule0/tag12 equalityReplace annotation [template,t,u]. -/
def line {n : Nat} (a b : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (formulaRaw a b)
   (applyTwo HistoryCodec.pair (constant n 0)
    (applyTwo HistoryCodec.pair (constant n 12)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons (templateRaw a)
       (applyTwo HistoryCodec.cons a (applyTwo HistoryCodec.cons b (constant n 0))))
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor : Program 2 := line (.projection 0) (.projection 1)
def leftTermCode : Program 1 := RawAddSucc.secondTermCode
def rightTermCode : Program 1 := applyOne HistoryLookup.head
 (applyOne HistoryLookup.tail (applyOne HistoryLookup.tail TwoSol20261113.ReflexivityRecognizer.argsCode))
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (line leftTermCode rightTermCode))
 (conjunction (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator leftTermCode)
  (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator rightTermCode))
def logicalLeaf (old : Program 1) : Program 1 := choose recognizer old (constant 1 1)
def nativeTemplate (a : List Nat) : List Nat :=
 GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.unary 2 a) [2,0,0]
def nativeFormula (a b : List Nat) : List Nat :=
 GorbowCodeConstructors.binary 7 (GorbowCodeConstructors.binary 0 a b)
  (GorbowCodeConstructors.binary 7
   (GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.unary 2 a) (GorbowCodeConstructors.unary 2 a))
   (GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.unary 2 a) (GorbowCodeConstructors.unary 2 b)))
def nativeLine (a b : List Nat) : GorbowProofChecker.Line :=
 (0,nativeFormula a b,0,12,[nativeTemplate a,a,b],0,0)
def binaryValue {ctx : Nat} (ctag atag token : Nat) (a b : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral token) (HistoryAppend.appendCall atag a b)
def succValue {ctx : Nat} (ctag : Nat) (a : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag (Term.numeral 2) a
def templateValue {ctx : Nat} (ctag atag : Nat) (a : Term ctx) : Term ctx :=
 binaryValue ctag atag 0 (succValue ctag a)
  (succValue ctag (HistoryLookup.consCall ctag .zero (HistoryLookup.consCall ctag .zero .zero)))
def formulaValue {ctx : Nat} (ctag atag : Nat) (a b : Term ctx) : Term ctx :=
 binaryValue ctag atag 7 (binaryValue ctag atag 0 a b)
  (binaryValue ctag atag 7 (binaryValue ctag atag 0 (succValue ctag a) (succValue ctag a))
   (binaryValue ctag atag 0 (succValue ctag a) (succValue ctag b)))
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (a b : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (formulaValue ctag atag a b)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 12)
     (HistoryKernel.pairCall ptag
      (HistoryLookup.consCall ctag (templateValue ctag atag a)
       (HistoryLookup.consCall ctag a (HistoryLookup.consCall ctag b .zero)))
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (a b : Term ctx) : Term ctx := call tag (a ::ᵥ b ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawSuccReplace
