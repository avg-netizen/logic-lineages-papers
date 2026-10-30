module
public import LogicLineages.OrdinalComparison.WWTypedPartialDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.Targets

/-! Bounded syntactic supplier for the literal WW partial clauses in paper05
foundations.tex331–354. Success on all generated canonical inputs, named-source
correspondence, and norm/effectivity obligations are not assumed here. -/
def ActualTypedHeadFreeCalibration : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ :: Γ)),
    ordinalHeadFree t = true ↔
      ordinalExpressionRename (Renaming.weaken Γ σ) (ordinalHeadClosure t) = t

def ActualTypedPartialSize : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (t : OrdinalExpression (σ :: Γ)),
    0 < ordinalPartialSize t ∧ (ordinalHeadFree t = true → ordinalPartialSize t = 1)

def ActualTypedFreePartial : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (t : OrdinalExpression (σ :: Γ)),
    ordinalHeadFree t = true →
      ordinalTypedPartial i t = some (ordinalFreePartialVector i t)

def ActualTypedVariablePartial : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (k : Fin (σ.level + 1)),
    ordinalTypedPartial (Γ := Γ) (σ := σ) i (.var ⟨σ, .here, k⟩) =
      if i = k.val then some (fun _ => .one) else none

def ActualTypedSumPartial : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (f g : OrdinalExpression (σ :: Γ)),
    ordinalHeadFree (.add f g) = false →
      ordinalTypedPartial i (.add f g) = (do
        let pf ← ordinalTypedPartial i f
        let pg ← ordinalTypedPartial i g
        pure fun j => .add (.add (pf j) (pg j)) .one)

def ActualTypedExponentialPartial : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (f g : OrdinalExpression (σ :: Γ)),
    ordinalHeadFree (.emul f g) = false →
      ordinalTypedPartial i (.emul f g) =
        if 0 < i then (do
          let pf ← ordinalTypedPartial (i + 1) f
          let pg ← ordinalTypedPartial i g
          pure fun j => .add (.add (.add (pf j) (pf j)) (pg j)) .one)
        else none

def ActualTypedCollapsePartial : Prop :=
  ∀ (Γ : List Ty) (σ : Ty) (i : Nat) (f g : OrdinalExpression (σ :: Γ)),
    ordinalHeadFree (.collapse f g) = false →
      ordinalTypedPartial i (.collapse f g) =
        if i = 0 then (do
          let pf ← ordinalTypedPartial 1 f
          let pg ← ordinalTypedPartial 0 g
          pure fun j => if j.val = 0 then .collapse (ordinalHeadClosure f) (pg 0)
            else .add (pf j) (pg j))
        else none

end LogicLineages.OrdinalComparison.Source.Targets
