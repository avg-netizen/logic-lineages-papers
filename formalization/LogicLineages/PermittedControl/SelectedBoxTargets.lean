module
public import LogicLineages.PermittedControl.SelectedBoundedDeltaDefinitions
public import LogicLineages.PermittedControl.CountDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedBoxTargets
open OrdinalComparison Source SelectedSourceDomain SelectedBoundedDelta
open Source.AdmissibleSum Source.AdmissibleAssignment

/-- Literal optional numeral role is absent at n=0; no zero tree is inserted. -/
def TailGradeAndNorm : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty) (p : Policy)
    (n : Nat) (f g : OrdinalExpression Γ),
    AmbientGrade ctrl Γ 0 f → AmbientGrade ctrl Γ 0 g →
    AmbientGrade ctrl Γ 0 (boxTail p n f g) ∧
    ∀ ρ : AdmissibleSubstitution ctrl Γ,
      actualOrdinalNorm (expressionValue ctrl ρ (boxTail p n f g)) =
        actualOrdinalNorm (expressionValue ctrl ρ f) + actualOrdinalNorm (expressionValue ctrl ρ g) + n

def HeadTailGrade : Prop := ∀ (ctrl : Nat → Nat) (Γ : List Ty) (σ : Ty) (p : Policy)
    (n : Nat) (f g : OrdinalExpression (σ :: Γ)),
    HeadGrade ctrl Γ σ 0 f → HeadGrade ctrl Γ σ 0 g →
    HeadGrade ctrl Γ σ 0 (boxTail p n f g)

/-- Actual universal F2 grammar guard is a conclusion, not a box premise. -/
def BoxGuard : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (m n : Nat), n < m → ∀ (p : Policy)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
    (∀ j, AmbientGrade ctrl Γ j.val (f j)) →
    (∀ j, AmbientGrade ctrl Γ j.val (g j)) →
    SourceBoundedVector ctrl f → SourceBoundedVector ctrl g →
    CollapseNormPremise ctrl
      (ordinalBoxPositive n (ordinalVectorAt f) (ordinalVectorAt g) 1)
      (boxTail p n (f 0) (g 0))

def AmbientBox : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (m n : Nat), n < m → ∀ (p : Policy)
    (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
    (∀ j, AmbientGrade ctrl Γ j.val (f j)) →
    (∀ j, AmbientGrade ctrl Γ j.val (g j)) →
    SourceBoundedVector ctrl f → SourceBoundedVector ctrl g →
    (∀ j, AmbientGrade ctrl Γ j.val (box p f g j)) ∧ SourceBoundedVector ctrl (box p f g)

/-- The source's second clause is actual head grammar, not ambient inclusion backwards. -/
def HeadBox : Prop := ∀ (ctrl : Nat → Nat) (K : Nat), SelectedWithThreshold ctrl K →
  ∀ (Γ : List Ty) (σ : Ty) (m n : Nat), n < m → ∀ (p : Policy)
    (f : OrdinalVector (σ :: Γ) m) (g : OrdinalVector (σ :: Γ) n),
    (∀ j, HeadGrade ctrl Γ σ j.val (f j)) →
    (∀ j, HeadGrade ctrl Γ σ j.val (g j)) →
    SourceBoundedVector ctrl f → SourceBoundedVector ctrl g →
    (∀ j, HeadGrade ctrl Γ σ j.val (box p f g j)) ∧ SourceBoundedVector ctrl (box p f g)

def FullSelectedBox : Prop := TailGradeAndNorm ∧ HeadTailGrade ∧ BoxGuard ∧ AmbientBox ∧ HeadBox

end LogicLineages.PermittedControl.SelectedBoxTargets
