module
public import LogicLineages.StandardControlCurrent.PolicyLevelTwoDefinitions
public import LogicLineages.OrdinalComparison.WWSourceScalarHeadProfileDefinitions
public import LogicLineages.OrdinalComparison.RawComparisonDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFinite
open OrdinalComparison Source Source.ForwardTranslation Source.AdmissibleSum Source.SourceClasses
open LevelTwoCounterexample

/-- Exact actual direct coefficient condition, including nested/repeated shifts. -/
def FiniteScalar {ι : Type} (s : Scalar ι) : Prop :=
  ∀ c ∈ scalarHeads s, c.evaluate.1.repr < Ordinal.omega0

/-- Property of the actual literal canonical scalar. Existence is required,
not vacuous truth on a failed assignment or extraction. -/
def FiniteSource {Γ : List Ty} {τ : Ty} (p : Policy) (t : OriginalTerm Γ τ) : Prop :=
  ∃ (v : OrdinalVector Γ τ.level) (s : Scalar (OrdinalComponent Γ)),
    AdmissibleAssignment.assignment p t=some v ∧ compileScalar (v 0)=some s ∧ FiniteScalar s

/-- Every literal scalar coefficient is evaluated and compared with omega.
Only scalar-tail recursion is needed at a shift; the head is closed syntax. -/
def finiteScalarCode : Nat → Bool
  | n =>
    if h : n%4=2 ∨ n%4=3 then
      have hn : 0<n := by omega
      have hd : n/4<n := Nat.div_lt_self hn (by decide)
      let q := (n/4).unpair
      have hl : q.1<n := (Nat.unpair_left_le _).trans_lt hd
      have hr : q.2<n := (Nat.unpair_right_le _).trans_lt hd
      if n%4=2 then finiteScalarCode q.1 && finiteScalarCode q.2
      else decide (rawComparisonCode (encodedClosedPositive q.1)
        (rawNoteEncode (.oadd 1 1 .zero))=0) && finiteScalarCode q.2
    else true
termination_by n => n
decreasing_by all_goals assumption

def accepts (p : Policy) (q : SourceCode.Input) : Bool :=
  (PolicySourceEquality.compileSyntax p q.1 q.2.2.1 q.2.2.2).any
    (fun syn => finiteScalarCode syn.2.1.1 && finiteScalarCode syn.2.2.1)

def admittedCompile (p : Policy) (q : SourceCode.Input) : Option Pair.Package :=
  if accepts p q then PolicyLevelTwo.compile p q else none

noncomputable def decision (p : Policy) (q : SourceCode.Input) : Option Bool :=
  (admittedCompile p q).map (fun pack => !(LevelTwoDecisionCompletion.packageCounterexample pack))

noncomputable def solve (p : Policy) (q : SourceCode.Input) : Bool := (decision p q).getD false
end LogicLineages.StandardControlCurrent.PolicyFinite
