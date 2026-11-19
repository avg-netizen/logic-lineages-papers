module
public import LogicLineages.ControlSensitivityCurrent.CurrentTreeInputCoverageDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionDefinitions
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentation

open LogicLineages.OrdinalComparison.Source
open GroundEquivalence
open OriginalInput (Query context)

/-- The independent original tree comparison, with no DAG in its domain or
definition. At ground-only contexts all original coordinates are positive
naturals; strictness affects only the scalar test, not positive coordinates. -/
noncomputable def OriginalUniversal (p : AdmissibleSum.Policy) (f : Nat → Nat)
    (strict : Bool) {Γ σ τ}
    (a : OriginalTerm Γ σ) (b : OriginalTerm Γ τ) : Prop :=
  ∃ (av : OrdinalVector Γ σ.level) (bv : OrdinalVector Γ τ.level),
    AdmissibleAssignment.assignment p a = some av ∧
    AdmissibleAssignment.assignment p b = some bv ∧
    ∀ ν : OrdinalComponent Γ → Nat, (∀ c, 0 < ν c) →
      CurrentCounterBound.compareAt f strict av bv ν

def rawContext (n : Nat) : List Nat := List.replicate n 0

def toDAGs (q : Query) : Option CurrentDecision.QueryCode := do
  let a ← CurrentTreeInputCoverage.compile (rawContext q.1) q.2.2.1
  let b ← CurrentTreeInputCoverage.compile (rawContext q.1) q.2.2.2
  return (q.2.1,a,b)

noncomputable def toArithmetic (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : Query) :
    Option CurrentDecision.ArithmeticCode :=
  (toDAGs q).map (CurrentDecision.toArithmetic p f)

noncomputable def toGround (p : AdmissibleSum.Policy) (f : Nat → Nat) (q : Query) :
    Option RawSourceDAG.PlanComparison.OutputCode :=
  (toArithmetic p f q).map CurrentCompiler.compile

end LogicLineages.ControlSensitivityCurrent.CurrentDecisionTreePresentation
