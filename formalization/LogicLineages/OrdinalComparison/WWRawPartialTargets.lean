module
public import LogicLineages.OrdinalComparison.WWRawPartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

def ActualTypedHeadReplacementCalibration : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ :: Γ)),
    ordinalHeadReplacement t =
      ordinalExpressionRename (Renaming.weaken Γ σ) (ordinalHeadClosure t)

def ActualRawPartialErasureCalibration : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    ordinalRawPartial i t = (ordinalTypedPartial i t).map ordinalPartialWeaken

def ActualRawPartialHeadFreeRecovery : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ))
      (v : OrdinalRawPartialVector Γ σ), ordinalRawPartial i t = some v →
    (∀ j, ordinalHeadFree (v j) = true) ∧
      ordinalTypedPartial i t = some (fun j => ordinalHeadClosure (v j))

end LogicLineages.OrdinalComparison.Source.Targets
