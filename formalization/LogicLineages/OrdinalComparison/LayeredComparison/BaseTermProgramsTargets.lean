module
public import LogicLineages.OrdinalComparison.LayeredComparison.BaseTermProgramsDefinitions
public import Mathlib.Computability.Partrec
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BaseTermPrograms.Targets
open CommonLayerSyntax
/-- Real all-code closed BASE evaluation and support extraction. Phi is ACTUAL
source control, table lookup is finite numeric data, with no value oracle. -/
def ActualComputation:Prop:=Computable₂ valueCode∧Computable variablesCode
/-- Exact finite numeric recursion, not a supplied mathematical/effectivity law. -/
def FiniteCallEquation:Prop:=
  (∀p q,q∈children p→q.1<p.1)∧∀p,joint p=assemble p ((children p).map joint)
def NumericalInterfaces:Prop:=Computable children∧Computable₂ assemble
/-- Two original raw assignments agreeing on ACTUAL syntax support give the
same value; this pays finite-point replacement, with outside vars unrestricted. -/
def SupportStability:Prop:=∀E:BaseTerm,∀ν μ:Nat→Nat,
  (∀i∈E.variables,ν i=μ i)→E.value ν=E.value μ
/-- Actual raw support domination, required by the source balanced finite box.
It is proved from literal syntax/Phi and is NOT a certificate hypothesis. -/
def SupportDomination:Prop:=∀E:BaseTerm,∀ν:Nat→Nat,∀i∈E.variables,ν i≤E.value ν
end LogicLineages.OrdinalComparison.LayeredComparison.BaseTermPrograms.Targets
