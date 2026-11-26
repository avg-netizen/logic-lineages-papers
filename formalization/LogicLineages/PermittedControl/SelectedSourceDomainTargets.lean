module
public import LogicLineages.PermittedControl.SelectedSourceDomainDefinitions
public import LogicLineages.PermittedControl.LiteralCovarianceDefinitions
public import LogicLineages.OrdinalComparison.WWLiteralPartialDomainDefinitions
public import LogicLineages.OrdinalComparison.WWLiteralSizeDefinitions

@[expose] public section
namespace LogicLineages.PermittedControl.SelectedSourceDomainTargets
open OrdinalComparison Source Source.AdmissibleSum SelectedSourceDomain

def HeadDomain : Prop := ∀ (f : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (i : Nat) (t : OrdinalExpression (σ::Γ)),
  HeadGrade f Γ σ i t → LiteralPartialDomain.Domain Γ σ i t

def HighCoordinateFree : Prop := ∀ (f : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (i : Nat) (t : OrdinalExpression (σ::Γ)),
  HeadGrade f Γ σ i t → σ.level < i →
    ordinalHeadFree t = true ∧ LiteralCovariance.weaken σ (ordinalHeadClosure t) = t

def UniquePartial : Prop := ∀ (f : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (p : Policy) (i : Nat) (t : OrdinalExpression (σ::Γ)),
  HeadGrade f Γ σ i t → ∃! v : OrdinalPartialVector Γ σ,
    AdmissiblePartial.run p i t = some v ∧
      ∀ j, ordinalLiteralNodes (v j) ≤ 6*3^ordinalLiteralNodes t

def UniqueVectorOperations : Prop := ∀ (f : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (p : Policy) (m : Nat) (h : OrdinalVector (σ::Γ) m),
  (∀ i, HeadGrade f Γ σ i.val (h i)) →
    (∃! ps : Fin (m+1) → OrdinalPartialVector Γ σ,
      AdmissibleAssignment.collect (m+1) (fun i => AdmissiblePartial.run p i.val (h i)) = some ps) ∧
    (∃! v : OrdinalVector Γ (max (σ.level+1) m), LiteralCovariance.delta p h = some v) ∧
    (∃! v : OrdinalVector Γ (max (σ.level+1) m), AdmissibleAssignment.abstraction p h = some v)

def DeltaHighRetention : Prop := ∀ (f : Nat → Nat) (Γ : List Ty) (σ : Ty)
    (p : Policy) (m : Nat) (h : OrdinalVector (σ::Γ) m),
  (∀ i, HeadGrade f Γ σ i.val (h i)) →
  ∀ (v : OrdinalVector Γ (max (σ.level+1) m)), LiteralCovariance.delta p h = some v →
  ∀ (j : Fin (max (σ.level+1) m+1)) (hj : σ.level+1 < j.val) (hm : j.val < m+1),
    LiteralCovariance.weaken σ (v j) = h ⟨j.val,hm⟩

/-- Supporting actual f-grade admission only; no output semantic norm theorem. -/
def FullSelectedSourceDomain : Prop :=
  HeadDomain ∧ HighCoordinateFree ∧ UniquePartial ∧ UniqueVectorOperations ∧ DeltaHighRetention

end LogicLineages.PermittedControl.SelectedSourceDomainTargets
