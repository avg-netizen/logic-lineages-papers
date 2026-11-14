module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawJointSource.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Original prefix term/formula constructors, at arbitrary runtime arity. -/
def successorRaw {n : Nat} (term : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n 2) term
def additionRaw {n : Nat} (left right : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n 3) (applyTwo HistoryAppend.append left right)
def equalityRaw {n : Nat} (left right : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n 0)
  (applyTwo HistoryAppend.append (additionRaw left (successorRaw right))
   (successorRaw (additionRaw left right)))
/-- Original context0/rule1/tag3/two-argument addSucc axiom, zero references. -/
def line {n : Nat} (left right : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (equalityRaw left right)
   (applyTwo HistoryCodec.pair (constant n 1)
    (applyTwo HistoryCodec.pair (constant n 3)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons left (applyTwo HistoryCodec.cons right (constant n 0)))
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor : Program 2 := line (.projection 0) (.projection 1)
def secondTermCode : Program 1 := applyOne HistoryLookup.head
 (applyOne HistoryLookup.tail TwoSol20261113.ReflexivityRecognizer.argsCode)
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0)
  (line TwoSol20261113.ReflexivityRecognizer.termCode secondTermCode))
 (conjunction
  (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator TwoSol20261113.ReflexivityRecognizer.termCode)
  (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator secondTermCode))
/-- Every input not matching this actual schema retains the prior arithmetic leaf. -/
def arithmeticLeaf (old : Program 1) : Program 1 := choose recognizer old (constant 1 1)
def nativeLine (left right : List Nat) : GorbowProofChecker.Line :=
 (0,GorbowCodeConstructors.binary 0
   (GorbowCodeConstructors.binary 3 left (GorbowCodeConstructors.unary 2 right))
   (GorbowCodeConstructors.unary 2 (GorbowCodeConstructors.binary 3 left right)),
  1,3,[left,right],0,0)
def equalityValue {ctx : Nat} (ctag atag : Nat) (left right : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero
  (HistoryAppend.appendCall atag
   (HistoryLookup.consCall ctag (Term.numeral 3)
    (HistoryAppend.appendCall atag left (HistoryLookup.consCall ctag (Term.numeral 2) right)))
   (HistoryLookup.consCall ctag (Term.numeral 2)
    (HistoryLookup.consCall ctag (Term.numeral 3) (HistoryAppend.appendCall atag left right))))
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (left right : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (equalityValue ctag atag left right)
   (HistoryKernel.pairCall ptag (.succ .zero)
    (HistoryKernel.pairCall ptag (Term.numeral 3)
     (HistoryKernel.pairCall ptag
      (HistoryLookup.consCall ctag left (HistoryLookup.consCall ctag right .zero))
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (left right : Term ctx) : Term ctx := call tag (left ::ᵥ right ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddSucc
