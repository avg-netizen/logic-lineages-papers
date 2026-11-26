module
public import LogicLineages.StandardControlCurrent.PolicyFiniteDefinitions
public import LogicLineages.StandardControlCurrent.PolicyShapeDefinitions
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyFiniteTargets
open OrdinalComparison Source Source.ForwardTranslation Source.AdmissibleSum Source.SourceClasses
open LevelTwoCounterexample

def CoefficientCheck : Prop := Computable PolicyFinite.finiteScalarCode ∧
  ∀ (ι : Type) (index : ι → Nat) (s : Scalar ι),
    PolicyFinite.finiteScalarCode (scalarSyntaxCode index s)=true ↔ PolicyFinite.FiniteScalar s

def Programs : Prop := ∀ p : Policy, PolicyShape.Effective p →
  Computable (PolicyFinite.accepts p) ∧ Computable (PolicyFinite.admittedCompile p) ∧
  Computable (PolicyFinite.decision p) ∧ Computable (PolicyFinite.solve p)

def ExactClass : Prop := ∀ (p : Policy) (q : SourceCode.Input),
  (PolicyFinite.accepts p q=true ↔
    ∃ (τ υ : Ty) (a : OriginalTerm (List.replicate q.1 Ty.ground) τ)
      (b : OriginalTerm (List.replicate q.1 Ty.ground) υ),
      SyntaxCode.encodeTerm a=q.2.2.1 ∧ SyntaxCode.encodeTerm b=q.2.2.2 ∧
      PolicyFinite.FiniteSource p a ∧ PolicyFinite.FiniteSource p b) ∧
  (PolicyFinite.decision p q).isSome=PolicyFinite.accepts p q ∧
  (PolicyFinite.accepts p q=false → PolicyFinite.decision p q=none ∧ PolicyFinite.solve p q=false)

/-- Every actual coefficient is checked, not a recursor ban or type-level test. -/
def TypedDecision : Prop := ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ,σ=Ty.ground) →
  ∀ (τ υ : Ty) (a : OriginalTerm Γ τ) (b : OriginalTerm Γ υ),
  PolicyFinite.FiniteSource p a → PolicyFinite.FiniteSource p b → ∀ mode : Nat,
  ∃ (av : OrdinalVector Γ τ.level) (bv : OrdinalVector Γ υ.level),
    AdmissibleAssignment.assignment p a=some av ∧ AdmissibleAssignment.assignment p b=some bv ∧
    PolicyFinite.decision p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=
      some (PolicyFinite.solve p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)) ∧
    (PolicyFinite.solve p (Γ.length,mode,SyntaxCode.encodeTerm a,SyntaxCode.encodeTerm b)=true ↔
      ∀ s : OriginalDomain.AdmissibleSubstitution Γ, PolicyLevelTwo.originalRelation mode av bv s)

/-- Source recursor absence implies every nested direct scalar coefficient is
finite at arbitrary internal levels, not only final positive outputs. -/
def RecursorFreeClass : Prop := ∀ (p : Policy) (Γ : List Ty), (∀ σ ∈ Γ,σ=Ty.ground) →
  ∀ (τ : Ty) (t : OriginalTerm Γ τ), recursorFree t=true → PolicyFinite.FiniteSource p t

/-- Entire current thm:source-finite, with actual decidable class and the
recursor-free corollary, using a complete polynomial-graph solver alternative. -/
def Full : Prop := CoefficientCheck ∧ Programs ∧ ExactClass ∧ TypedDecision ∧ RecursorFreeClass
end LogicLineages.StandardControlCurrent.PolicyFiniteTargets
