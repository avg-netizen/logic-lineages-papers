module
public import LogicLineages.StandardControlCurrent.PolicyOneNameDefinitions
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyOneNameTargets
open OrdinalComparison Source Source.AdmissibleSum Source.OriginalDomain

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (PolicyOneName.encodedOneNameSourceBooleanProgram p) ∧
  Computable₂ (PolicyOneName.encodedOneNameSourceBooleanValue p) ∧
  Computable (PolicyOneName.encodedOneNameSourceBooleanClosures p)

def NumericValue : Prop := ∀ (p : Policy) (formula : OneNameSourceBooleanExpr) (x : Nat), 0<x →
  PolicyOneName.encodedOneNameSourceBooleanValue p (oneNameSourceBooleanCompile formula) x=
    PolicyOneName.actualOneNameSourceBooleanValue p formula x

/-- Original substitutions evaluated as components, never source substitution
followed by recomputing a different assignment. -/
def OriginalValue : Prop := ∀ (p : Policy) (formula : OneNameSourceBooleanExpr)
  (s : AdmissibleSubstitution [Ty.ground]) (x : Nat),
  (∀ c, valuation s c=(x : Ordinal)) →
    PolicyOneName.originalValue p formula s=PolicyOneName.actualOneNameSourceBooleanValue p formula x

def Closures : Prop := ∀ (p : Policy) (formula : OneNameSourceBooleanExpr),
  let flags := PolicyOneName.encodedOneNameSourceBooleanClosures p (oneNameSourceBooleanCompile formula)
  (flags.1=true ↔ ∃ s : AdmissibleSubstitution [Ty.ground], PolicyOneName.originalValue p formula s=true) ∧
  (flags.2=true ↔ ∀ s : AdmissibleSubstitution [Ty.ground], PolicyOneName.originalValue p formula s=true)

/-- Entire current one-name Boolean corollary, arbitrary internal/result types,
all atoms sharing one ground input, actual original domain and both closures. -/
def Full : Prop := Programs ∧ NumericValue ∧ OriginalValue ∧ Closures
end LogicLineages.StandardControlCurrent.PolicyOneNameTargets
