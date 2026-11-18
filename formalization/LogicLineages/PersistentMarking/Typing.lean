import LogicLineages.PersistentMarking.Syntax

namespace LogicLineages.PersistentMarking

abbrev Context := Nat → Option Ty

def Context.bind (Γ : Context) (name : Nat) (type : Ty) : Context :=
  fun x => if x = name then some type else Γ x

mutual
  /-- Literal typing of auxiliary syntax. Original head declarations remain
  checked even when a marked node carries another output annotation. -/
  inductive Typed : Context → Term → Ty → Prop where
    | var : Γ x = some σ → Typed Γ (.var σ x) σ
    | lam : Typed (Γ.bind x σ) body τ →
        Typed Γ (.lam σ x body) (.arrow σ τ)
    | head : BaseTyped Γ base f.arguments →
        Typed Γ (.head f base) f.result
    | marked : BaseTyped Γ base f.arguments → ExtrasTyped Γ extras →
        Typed Γ (.marked f τ base extras) τ
  inductive BaseTyped : Context → List Term → List Ty → Prop where
    | nil : BaseTyped Γ [] []
    | cons : Typed Γ s σ → BaseTyped Γ ss σs →
        BaseTyped Γ (s :: ss) (σ :: σs)
  inductive ExtrasTyped : Context → List Term → Prop where
    | nil : ExtrasTyped Γ []
    | cons : Typed Γ s σ → ExtrasTyped Γ ss → ExtrasTyped Γ (s :: ss)
end

end LogicLineages.PersistentMarking
