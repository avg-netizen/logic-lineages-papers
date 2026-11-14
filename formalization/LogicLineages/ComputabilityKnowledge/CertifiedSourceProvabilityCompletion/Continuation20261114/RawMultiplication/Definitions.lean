module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawNumeralAddition.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
namespace Zero
/-- Original term token1 is zero; token4 is multiplication; formula token0 is equality. -/
def zeroRaw : Program 1 := applyTwo HistoryCodec.cons (constant 1 1) (constant 1 0)
def mulZeroRaw (term : Program 1) : Program 1 :=
 applyTwo HistoryCodec.cons (constant 1 4) (applyTwo HistoryAppend.append term zeroRaw)
def equalityRaw (term : Program 1) : Program 1 :=
 applyTwo HistoryCodec.cons (constant 1 0) (applyTwo HistoryAppend.append (mulZeroRaw term) zeroRaw)
/-- Literal original arithmetic line: context0, rule1, annotation tag4, singleton
raw-term argument, zero references. The formula is t*0=0, not reflexivity. -/
def line (term : Program 1) : Program 1 :=
 applyTwo HistoryCodec.pair (constant 1 0)
  (applyTwo HistoryCodec.pair (equalityRaw term)
   (applyTwo HistoryCodec.pair (constant 1 1)
    (applyTwo HistoryCodec.pair (constant 1 4)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons term (constant 1 0))
      (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0))))))
def lineConstructor : Program 1 := line (.projection 0)
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (line TwoSol20261113.ReflexivityRecognizer.termCode))
 (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator TwoSol20261113.ReflexivityRecognizer.termCode)
/-- Only the explicitly recognized original mul-zero axiom takes the positive
branch. Every other input retains the whole old arithmetic leaf. -/
def arithmeticLeaf (old : Program 1) : Program 1 := choose recognizer old (constant 1 1)
def nativeLine (raw : List Nat) : GorbowProofChecker.Line :=
 (0,GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.binary 4 raw [1]) [1],1,4,[raw],0,0)
def equalityValue {ctx : Nat} (ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero
  (HistoryAppend.appendCall atag
   (HistoryLookup.consCall ctag (Term.numeral 4)
    (HistoryAppend.appendCall atag raw (HistoryLookup.consCall ctag (.succ .zero) .zero)))
   (HistoryLookup.consCall ctag (.succ .zero) .zero))
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (equalityValue ctag atag raw)
   (HistoryKernel.pairCall ptag (.succ .zero)
    (HistoryKernel.pairCall ptag (Term.numeral 4)
     (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag raw .zero)
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (raw : Term ctx) : Term ctx := call tag (raw ::ᵥ nil)
end Zero
namespace Succ
/-- Original prefix term/formula constructors, at arbitrary runtime arity. -/
def successorRaw {n : Nat} (term : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n 2) term
def multiplicationRaw {n : Nat} (left right : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n 4) (applyTwo HistoryAppend.append left right)
def equalityRaw {n : Nat} (left right : Program n) : Program n :=
 applyTwo HistoryCodec.cons (constant n 0)
  (applyTwo HistoryAppend.append (multiplicationRaw left (successorRaw right))
   (RawAddSucc.additionRaw (multiplicationRaw left right) left))
/-- Original context0/rule1/tag5/two-argument mulSucc axiom, zero references. -/
def line {n : Nat} (left right : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (equalityRaw left right)
   (applyTwo HistoryCodec.pair (constant n 1)
    (applyTwo HistoryCodec.pair (constant n 5)
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
   (GorbowCodeConstructors.binary 4 left (GorbowCodeConstructors.unary 2 right))
   (GorbowCodeConstructors.binary 3 (GorbowCodeConstructors.binary 4 left right) left),
  1,5,[left,right],0,0)
def equalityValue {ctx : Nat} (ctag atag : Nat) (left right : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero
  (HistoryAppend.appendCall atag
   (HistoryLookup.consCall ctag (Term.numeral 4)
    (HistoryAppend.appendCall atag left (HistoryLookup.consCall ctag (Term.numeral 2) right)))
   (HistoryLookup.consCall ctag (Term.numeral 3)
    (HistoryAppend.appendCall atag
     (HistoryLookup.consCall ctag (Term.numeral 4) (HistoryAppend.appendCall atag left right)) left)))
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (left right : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (equalityValue ctag atag left right)
   (HistoryKernel.pairCall ptag (.succ .zero)
    (HistoryKernel.pairCall ptag (Term.numeral 5)
     (HistoryKernel.pairCall ptag
      (HistoryLookup.consCall ctag left (HistoryLookup.consCall ctag right .zero))
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (left right : Term ctx) : Term ctx := call tag (left ::ᵥ right ::ᵥ nil)
end Succ
/-- Both original multiplication schemas, preserving full prior arithmetic fallback. -/
def arithmeticLeaf (old : Program 1) : Program 1 := Succ.arithmeticLeaf (Zero.arithmeticLeaf old)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawMultiplication
