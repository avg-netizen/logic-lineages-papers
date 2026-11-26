module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedCase13.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261114
def arguments {n : Nat} (formula replacement : Program n) : Program n :=
 applyTwo HistoryCodec.cons formula (applyTwo HistoryCodec.cons replacement (constant n 0))
/-- None becomes empty raw-list code0; Some result becomes its actual code.
The logical recognizer separately checks both original validity guards. -/
def conclusion {n : Nat} (formula replacement : Program n) : Program n :=
 applyOne HistoryCodec.predecessor (applyOne UniformClosedCase13.caseCode (arguments formula replacement))
def line {n : Nat} (formula replacement : Program n) : Program n :=
 applyTwo HistoryCodec.pair (constant n 0)
  (applyTwo HistoryCodec.pair (conclusion formula replacement)
   (applyTwo HistoryCodec.pair (constant n 0)
    (applyTwo HistoryCodec.pair (constant n 13)
     (applyTwo HistoryCodec.pair (arguments formula replacement)
      (applyTwo HistoryCodec.pair (constant n 0) (constant n 0))))))
def lineConstructor : Program 2 := line (.projection 0) (.projection 1)
def recognizer : Program 1 := conjunction
 (applyTwo equalCode (.projection 0)
  (line TwoSol20261113.ReflexivityRecognizer.termCode RawAddSucc.secondTermCode))
 (conjunction
  (applyTwo LiteralSyntaxValidator.formulaValidator (constant 1 1) TwoSol20261113.ReflexivityRecognizer.termCode)
  (applyOne TwoSol20261113.ReflexivityRecognizer.termValidator RawAddSucc.secondTermCode))
/-- New explicit logical leaf retaining the exact previous fallback on every
unmatched input; not an identity assertion about the old opaque AST. -/
def logicalLeaf (old : Program 1) : Program 1 := choose recognizer old (constant 1 1)
def nativeLine (formula replacement : List Nat) : GorbowProofChecker.Line :=
 (0,(GorbowLogicalAxiomCode.case13 0 [formula,replacement]).getD [],0,13,[formula,replacement],0,0)
def argumentsValue {ctx : Nat} (ctag : Nat) (formula replacement : Term ctx) : Term ctx :=
 HistoryLookup.consCall ctag formula (HistoryLookup.consCall ctag replacement .zero)
def conclusionValue {ctx : Nat} (caseTag predTag ctag : Nat) (formula replacement : Term ctx) : Term ctx :=
 call predTag (UniformClosedCase13.caseCall caseTag (argumentsValue ctag formula replacement) ::ᵥ nil)
def lineValue {ctx : Nat} (caseTag predTag ptag ctag : Nat) (formula replacement : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag .zero
  (HistoryKernel.pairCall ptag (conclusionValue caseTag predTag ctag formula replacement)
   (HistoryKernel.pairCall ptag .zero
    (HistoryKernel.pairCall ptag (Term.numeral 13)
     (HistoryKernel.pairCall ptag (argumentsValue ctag formula replacement)
      (HistoryKernel.pairCall ptag .zero .zero)))))
def lineCall {ctx : Nat} (tag : Nat) (formula replacement : Term ctx) : Term ctx :=
 call tag (formula ::ᵥ replacement ::ᵥ nil)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedRule13
