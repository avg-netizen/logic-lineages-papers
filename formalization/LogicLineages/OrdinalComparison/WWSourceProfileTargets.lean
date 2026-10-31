module
public import LogicLineages.OrdinalComparison.WWSourceClassesDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets
open SourceClasses AdmissibleSum

def SourceHeadClosureProfile : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ :: Γ)),
    noOmega (ordinalHeadClosure t) = noOmega t ∧
      headHeight (ordinalHeadClosure t) = headHeight t

def SourcePartialNoOmega : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ),
    AdmissiblePartial.run p i t = some v → noOmega t = true →
      ∀ j, noOmega (v j) = true

def SourcePartialHeadHeight : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (p : Policy) (L i : Nat)
    (t : OrdinalExpression (σ :: Γ)) (v : OrdinalPartialVector Γ σ),
    AdmissiblePartial.run p i t = some v → headHeight t ≤ L - i →
      ∀ j, headHeight (v j) ≤ L - j.val

end LogicLineages.OrdinalComparison.Source.Targets
