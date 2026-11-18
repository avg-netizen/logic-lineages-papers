module
public import LogicLineages.PermittedControl.SelectedBoundedDeltaDefinitions
public import LogicLineages.PermittedControl.CountDefinitions
public import LogicLineages.StandardControlCurrent.PolicyAssignmentTargets

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedCanonicalDomainTargets
open OrdinalComparison Source SelectedSourceDomain SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment Source.OrdinalSyntax Source.SyntaxCode

/-- Generated positive syntax has no scalar promotion; actual f-valued guards remain mandatory. -/
def GeneratedAmbientHead : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    GeneratedOrdinalGrade (σ :: Γ) i t → AmbientGrade ctrl (σ :: Γ) i t → HeadGrade ctrl Γ σ i t

/-- Inner delta is supplemented by exactly the retained actual closure coordinates. -/
def AbstractionComposition : Prop := ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy)
    (h : OrdinalVector (σ :: Γ) m) (v : OrdinalVector Γ (max (σ.level+1) m)),
    LiteralCovariance.delta p h = some v →
    abstraction p h = some (fun j => if hm : j.val < m+1 then
      .add (v j) (ordinalHeadClosure (h ⟨j.val,hm⟩)) else v j)

def AbstractionBounded : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ j, HeadGrade ctrl Γ σ j.val (h j)) → SourceBoundedVector ctrl h →
    ∃ v : OrdinalVector Γ (max (σ.level+1) m), abstraction p h = some v ∧
      (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧ SourceBoundedVector ctrl v

def ApplicationBounded : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ τ : Ty) (p : Policy)
    (f : OrdinalVector Γ (Ty.arrow σ τ).level) (g : OrdinalVector Γ σ.level),
    (∀ j, AmbientGrade ctrl Γ j.val (f j)) →
    (∀ j, AmbientGrade ctrl Γ j.val (g j)) →
    SourceBoundedVector ctrl f → SourceBoundedVector ctrl g →
    (∀ j, AmbientGrade ctrl Γ j.val (application p f g j)) ∧
      SourceBoundedVector ctrl (application p f g)

/-- All literal terms, unrestricted finite internal and recursor types, with real code success. -/
def CanonicalAssignment : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (τ : Ty) (p : Policy) (t : OriginalTerm Γ τ),
    ∃ v : OrdinalVector Γ τ.level, assignment p t = some v ∧
      StandardControlCurrent.PolicyAssignment.assignmentCode p (Γ.map typeCode) (encodeTerm t) =
        some (vectorCode v) ∧
      (∀ j, GeneratedOrdinalGrade Γ j.val (v j)) ∧
      (∀ j, AmbientGrade ctrl Γ j.val (v j)) ∧ SourceBoundedVector ctrl v

/-- Every actual binder body supplies the head-sensitive domain required by delta. -/
def BinderBody : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ τ : Ty) (p : Policy) (body : OriginalTerm (σ :: Γ) τ),
    ∃ v : OrdinalVector (σ :: Γ) τ.level, assignment p body = some v ∧
      (∀ j, HeadGrade ctrl Γ σ j.val (v j)) ∧ SourceBoundedVector ctrl v

def FullSelectedCanonicalDomain : Prop := GeneratedAmbientHead ∧ AbstractionComposition ∧
  AbstractionBounded ∧ ApplicationBounded ∧ CanonicalAssignment ∧ BinderBody ∧
  StandardControlCurrent.PolicyAssignmentTargets.LiteralCalibration ∧
  StandardControlCurrent.PolicyAssignmentTargets.SourceExact ∧
  StandardControlCurrent.PolicyAssignmentTargets.Programs

end LogicLineages.PermittedControl.SelectedCanonicalDomainTargets
