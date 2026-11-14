module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawReflexivitySource.StatementChecks
public import LogicLineages.ComputabilityKnowledge.GorbowArithmeticAxiomCode
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations List.Vector SixSol20261113 HistoryRuleSuffix
/-- Original term token1 is zero; token3 is addition; formula token0 is equality. -/
def zeroRaw : Program 1 := applyTwo HistoryCodec.cons (constant 1 1) (constant 1 0)
def addZeroRaw (term : Program 1) : Program 1 :=
 applyTwo HistoryCodec.cons (constant 1 3) (applyTwo HistoryAppend.append term zeroRaw)
def equalityRaw (term : Program 1) : Program 1 :=
 applyTwo HistoryCodec.cons (constant 1 0) (applyTwo HistoryAppend.append (addZeroRaw term) term)
/-- Literal original arithmetic line: context0, rule1, annotation tag2, singleton
raw-term argument, zero references. The formula is t+0=t, not reflexivity. -/
def line (term : Program 1) : Program 1 :=
 applyTwo HistoryCodec.pair (constant 1 0)
  (applyTwo HistoryCodec.pair (equalityRaw term)
   (applyTwo HistoryCodec.pair (constant 1 1)
    (applyTwo HistoryCodec.pair (constant 1 2)
     (applyTwo HistoryCodec.pair
      (applyTwo HistoryCodec.cons term (constant 1 0))
      (applyTwo HistoryCodec.pair (constant 1 0) (constant 1 0))))))
def lineConstructor : Program 1 := line (.projection 0)
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0) (line TwoSol20261113.ReflexivityRecognizer.termCode))
 (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator TwoSol20261113.ReflexivityRecognizer.termCode)
/-- Only the explicitly recognized original add-zero axiom takes the positive
branch. Every other input retains the whole old arithmetic leaf. -/
def arithmeticLeaf (old : Program 1) : Program 1 := choose recognizer old (constant 1 1)
def nativeLine (raw : List Nat) : GorbowProofChecker.Line :=
 (0,GorbowCodeConstructors.binary 0 (GorbowCodeConstructors.binary 3 raw [1]) raw,1,2,[raw],0,0)
def equalityValue {ctx : Nat} (ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag .zero
  (HistoryAppend.appendCall atag
   (HistoryLookup.consCall ctag (Term.numeral 3)
    (HistoryAppend.appendCall atag raw (HistoryLookup.consCall ctag (.succ .zero) .zero))) raw)
def lineValue {ctx : Nat} (ptag ctag atag : Nat) (raw : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (equalityValue ctag atag raw)
   (HistoryKernel.pairCall ptag (.succ .zero)
    (HistoryKernel.pairCall ptag (Term.numeral 2)
     (HistoryKernel.pairCall ptag (HistoryLookup.consCall ctag raw .zero)
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (raw : Term ctx) : Term ctx := call tag (raw ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114.RawAddZero
