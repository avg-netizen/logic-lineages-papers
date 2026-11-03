module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluationDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Targets
open BalancedSyntax
/-- Exact actual closed-point evaluation/support for ORIGINAL finite balanced
certificates and ONE original finite raw table. No new independent basis vals. -/
def ActualSourceCalibration:Prop:=∀Γ:List Nat,∀C:Certificate Γ,∀E:Syntax Γ,∀table:Table,
  codeValue Γ (encodeCertificate Γ C) (encodeSyntax Γ E) table=
    value Γ C E (BaseTermPrograms.valuation table)∧
  codeVariables Γ (encodeCertificate Γ C) (encodeSyntax Γ E)=rawVariables Γ C E
/-- Genuine uniformly computable value AND raw-support extraction on ALL
shape/certificate/expression/table codes, not a supplied evaluator field. -/
def AllCodeComputation:Prop:=Computable (fun p:Input=>joint p)
def FiniteCallEquation:Prop:=
  (∀p q,q∈children p→q.1.length<p.1.length)∧∀p,joint p=assemble p ((children p).map joint)
def NumericalInterfaces:Prop:=Computable children∧Computable₂ assemble
end LogicLineages.OrdinalComparison.LayeredComparison.BalancedEvaluation.Targets
