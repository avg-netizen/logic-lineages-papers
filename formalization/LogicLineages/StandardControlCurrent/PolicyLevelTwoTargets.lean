module
public import LogicLineages.StandardControlCurrent.PolicyLevelTwoDefinitions
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyLevelTwoTargets
open OrdinalComparison Source Source.ForwardTranslation Source.AdmissibleSum Source.SourceClasses
open LevelTwoCounterexample

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (PolicyLevelTwo.compile p) ∧ Computable (PolicyLevelTwo.admittedCompile p) ∧
  Computable (PolicyLevelTwo.decision p) ∧ Computable (PolicyLevelTwo.solve p)

def ExactDomain : Prop := ∀ (p : Policy) (q : SourceCode.Input),
  (PolicyLevelTwo.decision p q).isSome=Admission.accepts q ∧
  (Admission.accepts q=false → PolicyLevelTwo.decision p q=none ∧ PolicyLevelTwo.solve p q=false)

/-- Actual original terms, all internal type/subtype bounds, derived assignments
and graph counterexample equivalence on the original domain, not a supplier. -/
def Counterexamples : Prop := ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ,σ=Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
  InternalLevelBound 2 a → InternalLevelBound 2 b → ∀ mode : Nat,
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level) (pack : Pair.Package),
    AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
    PolicyLevelTwo.admittedCompile p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=some pack ∧
    LevelTwoDecisionCompletion.PackageCertified pack ∧
    (Pair.Closed pack ↔ ∃ s : OriginalDomain.AdmissibleSubstitution Γ,
      ¬PolicyLevelTwo.originalRelation mode av bv s)

/-- Actual complete decision, with no compilation, head-profile, solver or
successful-admission oracle supplied by the caller. -/
def TypedDecision : Prop := ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ,σ=Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
  InternalLevelBound 2 a → InternalLevelBound 2 b → ∀ mode : Nat,
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
    AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
    PolicyLevelTwo.decision p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=
      some (PolicyLevelTwo.solve p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)) ∧
    (PolicyLevelTwo.solve p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=true ↔
      ∀ s : OriginalDomain.AdmissibleSubstitution Γ, PolicyLevelTwo.originalRelation mode av bv s)

/-- Entire current thm:source-leveltwo, not merely a graph compiler contract. -/
def Full : Prop := Programs ∧ ExactDomain ∧ Counterexamples ∧ TypedDecision
end LogicLineages.StandardControlCurrent.PolicyLevelTwoTargets
