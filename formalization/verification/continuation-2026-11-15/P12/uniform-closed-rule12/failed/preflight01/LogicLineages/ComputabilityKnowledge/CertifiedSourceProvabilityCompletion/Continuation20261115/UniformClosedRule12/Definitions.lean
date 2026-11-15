module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase12.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
open Continuation20261114
def arguments {n : Nat} (formula left right : Program n) : Program n :=
 applyTwo HistoryCodec.cons formula
  (applyTwo HistoryCodec.cons left (applyTwo HistoryCodec.cons right (constant n 0)))
def conclusion {n : Nat} (formula left right : Program n) : Program n :=
 applyOne HistoryCodec.predecessor (applyOne UniformClosedCase12.caseCode (arguments formula left right))
/-- Literal original rule0/tag12, three arguments and zero references. -/
def line {n : Nat} (formula left right : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (conclusion formula left right)
   (applyTwo HistoryCodec.pair (constant n 0)
    (applyTwo HistoryCodec.pair (constant n 12)
     (applyTwo HistoryCodec.pair (arguments formula left right)
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor : Program 3 := line (.projection 0) (.projection 1) (.projection 2)
def thirdTermCode : Program 1 := applyOne HistoryLookup.head
 (applyOne HistoryLookup.tail (applyOne HistoryLookup.tail TwoSol20261113.ReflexivityRecognizer.argsCode))
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0)
  (line TwoSol20261113.ReflexivityRecognizer.termCode RawAddSucc.secondTermCode thirdTermCode))
 (conjunction
  (applyTwo LiteralSyntaxValidator.formulaValidator (constant 1 1) TwoSol20261113.ReflexivityRecognizer.termCode)
  (conjunction
   (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator RawAddSucc.secondTermCode)
   (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator thirdTermCode)))
/-- The existing uniform case13 leaf remains the literal fallback, not an
assumed equality with an opaque original logical evaluator. -/
def logicalLeaf (old : Program 1) : Program 1 :=
 choose recognizer (UniformClosedRule13.logicalLeaf old) (constant 1 1)
def nativeLine (formula left right : List Nat) : GorbowProofChecker.Line :=
 (0,(GorbowLogicalAxiomCode.case12 0 [formula,left,right]).getD [],0,12,[formula,left,right],0,0)
def argumentsValue {ctx : Nat} (ctag : Nat) (formula left right : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag formula (HistoryLookup.consCall ctag left (HistoryLookup.consCall ctag right .zero))
def conclusionValue {ctx : Nat} (caseTag predTag ctag : Nat) (formula left right : Term ctx) : Term ctx :=
 call predTag (UniformClosedCase12.caseCall caseTag (argumentsValue ctag formula left right) ::ᵥ nil)
def lineValue {ctx : Nat} (caseTag predTag ptag ctag : Nat) (formula left right : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (conclusionValue caseTag predTag ctag formula left right)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 12)
     (HistoryKernel.pairCall ptag (argumentsValue ctag formula left right)
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (formula left right : Term ctx) : Term ctx :=
 call tag (formula ::ᵥ left ::ᵥ right ::ᵥ nil)
def guards {ctx : Nat} (fval vtag : Nat) (formula left right : Term ctx) : Formula ctx :=
 .conj (UniformClosedInstanceRecognizer.guards fval vtag formula left)
  (Continuation20261114.RawReflexivityDispatcher.valid vtag right)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule12
