module
public import LogicLineages.OrdinalComparison.FunctionalHardnessCompletion.SystemSourceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed
open OriginalDomain FunctionalDetector
abbrev higherUnary : Ty := .arrow unary unary

def higherIdentity {Γ : List Ty} : OriginalTerm Γ higherUnary := .lam (.var .here)
def higherLift {Γ : List Ty} (a : OriginalTerm Γ higherUnary) : OriginalTerm Γ higherUnary :=
  .app (.app (.recC unary) .zeroC) (.lam (a.rename (Renaming.weaken Γ .ground)))
def source {Γ : List Ty} : OriginalTerm Γ higherUnary :=
  higherLift (higherLift higherIdentity)

noncomputable def secondValue {Γ : List Ty} (ρ : AdmissibleSubstitution Γ)
    (a : OriginalTerm Γ higherUnary) : Ordinal :=
  ((AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy a).map
    (fun v => expressionValue ρ (v 2))).getD 0

def topStep (t : ClosedExpression) : ClosedExpression := .emul .omega (.add .one (.add t t))
def exponentExpression : ClosedExpression := topStep (topStep (.add .one .one))
def omegaExpression : ClosedExpression := .emul exponentExpression .one
noncomputable def exponent : Ordinal := closedValue exponentExpression
noncomputable def omega : Ordinal := closedValue omegaExpression

/-- Applying this one literal closed source to both entries of the accepted
constant pair produces the additional closed seed used by the level-three
compiler. No new ordinal-valued source primitive has been introduced. -/
def pair {Γ : List Ty} : SignedPair.Pair Γ :=
  (.app source SignedPair.unitPair.1, .app source SignedPair.unitPair.2)

end LogicLineages.OrdinalComparison.Source.FunctionalHardnessCompletion.OmegaSeed
