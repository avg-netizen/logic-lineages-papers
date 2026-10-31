module
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceClasses AdmissibleSum AdmissibleAssignment

def SourceBoxNoOmega : Prop :=
  ∀ (Γ : List Ty) (m n : Nat) (p : Policy) (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
    (∀ j, noOmega (f j) = true) → (∀ j, noOmega (g j) = true) →
      ∀ j, noOmega (box p f g j) = true

def SourceBoxHeadHeight : Prop :=
  ∀ (Γ : List Ty) (L m n : Nat), n < m → m ≤ L →
    ∀ (p : Policy) (f : OrdinalVector Γ m) (g : OrdinalVector Γ n),
      (∀ j, headHeight (f j) ≤ L - j.val) → (∀ j, headHeight (g j) ≤ L - j.val) →
        ∀ j, headHeight (box p f g j) ≤ L - j.val

def SourceAbstractionNoOmega : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m)
    (v : OrdinalVector Γ (max (σ.level + 1) m)),
    abstraction p h = some v → (∀ j, noOmega (h j) = true) → ∀ j, noOmega (v j) = true

def SourceAbstractionHeadHeight : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (L m : Nat) (p : Policy) (h : OrdinalVector (σ :: Γ) m)
    (v : OrdinalVector Γ (max (σ.level + 1) m)),
    abstraction p h = some v → (∀ j, headHeight (h j) ≤ L - j.val) →
      ∀ j, headHeight (v j) ≤ L - j.val

end LogicLineages.OrdinalComparison.Source.Targets
