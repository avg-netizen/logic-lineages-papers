module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformSubstitutionFormulaValidity.StatementChecks
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer
open GorbowSyntax GorbowPRProgram GorbowPRDefiningEquations SixSol20261113 HistoryRuleSuffix List.Vector
/-- Fixed before every source root/tag: inputs [formula raw-list code,
closed replacement raw-list code]. Literal original formula task (1,1). -/
def initialTask : Program 2 := applyTwo HistoryCodec.pair (constant 2 1) (constant 2 1)
def initialTasks : Program 2 := applyTwo HistoryCodec.cons initialTask (constant 2 0)
def initialState : Program 2 := applyTwo HistoryCodec.pair (applyOne .succ initialTasks) (constant 2 0)
def rawFold : Program 2 := .composition UniformClosedSubstitutionRawFold.foldCode
 (fun i => ((.projection 0) ::ᵥ initialState ::ᵥ (.projection 1) ::ᵥ nil).get i)
def outputCode : Program 2 := applyOne (HistoryDecoder.decoder true) rawFold
def formulaGuard : Program 2 := applyTwo LiteralSyntaxValidator.formulaValidator (constant 2 1) (.projection 0)
def termGuard : Program 2 := applyOne TwoSol20261113.ReflexivityRecognizer.termValidator (.projection 1)
/-- Equality-to-one guards retain exact Boolean validator meaning even for
arbitrary internal numeric outputs. None=0; Some output=successor(output). -/
def instanceCode : Program 2 :=
 choose (applyTwo equalCode formulaGuard (constant 2 1)) (constant 2 0)
  (choose (applyTwo equalCode termGuard (constant 2 1)) (constant 2 0)
   (applyOne .succ outputCode))
def instanceCall {ctx : Nat} (tag : Nat) (formula replacement : Term ctx) : Term ctx :=
 call tag (formula ::ᵥ replacement ::ᵥ nil)
def guards {ctx : Nat} (fval vtag : Nat) (formula replacement : Term ctx) : Formula ctx :=
 .conj (.equal (LiteralSyntaxValidator.formulaCall fval (.succ .zero) formula) (.succ .zero))
  (Continuation20261114.RawReflexivityDispatcher.valid vtag replacement)
def outputValue {ctx : Nat} (ftag ptag ctag rtag : Nat) (formula replacement : Term ctx) : Term ctx :=
 UniformSubstitutionFormulaValidity.substitutedOutput ftag ptag ctag rtag .zero formula replacement
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115.UniformClosedInstanceRecognizer
