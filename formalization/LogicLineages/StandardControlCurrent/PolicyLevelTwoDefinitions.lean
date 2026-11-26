module
public import LogicLineages.StandardControlCurrent.PolicySourceInterfaceDefinitions
public import LogicLineages.OrdinalComparison.LevelTwoDecisionCompletion.Definitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyLevelTwo
open OrdinalComparison Source Source.ForwardTranslation Source.AdmissibleSum
open LevelTwoCounterexample

/-- Literal arbitrary-policy assignment/extraction, followed by the actual
polynomial scalar lowering and correlated graph package. -/
def compile (p : Policy) (q : SourceCode.Input) : Option Pair.Package := do
  let a ← PolicySourceInterface.compile p q.1 q.2.2.1
  let b ← PolicySourceInterface.compile p q.1 q.2.2.2
  pure (Pair.Code.package (q.1,q.2.1,SourceCode.positiveFlag q.2.1 a b,
    ScalarCode.lowerSyntax a.1,ScalarCode.lowerSyntax b.1))

def admittedCompile (p : Policy) (q : SourceCode.Input) : Option Pair.Package :=
  if Admission.accepts q then compile p q else none

noncomputable def decision (p : Policy) (q : SourceCode.Input) : Option Bool :=
  (admittedCompile p q).map (fun package => !(LevelTwoDecisionCompletion.packageCounterexample package))

noncomputable def solve (p : Policy) (q : SourceCode.Input) : Bool := (decision p q).getD false

/-- Independent original admissible component semantics, retaining zero padding
and the WW strict convention, not a lexicographic comparison. -/
noncomputable def originalRelation {Γ : List Ty} {n m : Nat} (mode : Nat)
    (a : OrdinalVector Γ n) (b : OrdinalVector Γ m) (s : OriginalDomain.AdmissibleSubstitution Γ) : Prop :=
  if mode=0 then ∀ j, PolicySourceEquality.vectorAt a s j≤PolicySourceEquality.vectorAt b s j
  else if mode=1 then PolicySourceEquality.vectorAt a s 0<PolicySourceEquality.vectorAt b s 0 ∧
    ∀ j, PolicySourceEquality.vectorAt a s (j+1)≤PolicySourceEquality.vectorAt b s (j+1)
  else ∀ j, PolicySourceEquality.vectorAt a s j=PolicySourceEquality.vectorAt b s j
end LogicLineages.StandardControlCurrent.PolicyLevelTwo
