module
public import LogicLineages.OrdinalComparison.WWOriginalDeltaDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open OriginalDomain AdmissibleSum

def OriginalHigherCoordinateFree : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    HeadGrade Γ σ i t → σ.level < i → ordinalHeadFree t = true

def OriginalDeltaValid : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade Γ σ i.val (h i)) →
    ∃ v, delta p h = some v ∧ ∀ j, AmbientGrade Γ j.val (v j)

def OriginalSourceAbstractionValid : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m),
    (∀ i, HeadGrade Γ σ i.val (h i)) →
    ∃ v, AdmissibleAssignment.abstraction p h = some v ∧ ∀ j, AmbientGrade Γ j.val (v j)

/-- Exact relationship to the existing actual source-lambda implementation;
retained actual coordinates are added and absent roles are not looked up. -/
def OriginalDeltaAbstractionComposition : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m)
    (v : OrdinalVector Γ (max (σ.level + 1) m)), delta p h = some v →
    AdmissibleAssignment.abstraction p h = some (fun j =>
      if hm : j.val < m + 1 then .add (v j) (ordinalHeadClosure (h ⟨j.val, hm⟩)) else v j)

end LogicLineages.OrdinalComparison.Source.Targets
