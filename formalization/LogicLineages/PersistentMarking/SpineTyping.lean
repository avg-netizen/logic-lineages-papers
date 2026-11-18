import LogicLineages.PersistentMarking.SpineSyntax

namespace LogicLineages.PersistentMarking.Spine

abbrev BoundContext := Nat → Option Ty

namespace BoundContext

def push (Γ : BoundContext) (σ : Ty) : BoundContext
  | 0 => some σ
  | n+1 => Γ n

def prefix : List Ty → BoundContext → BoundContext
  | [], Γ => Γ
  | σ :: rest, Γ => (prefix rest Γ).push σ
end BoundContext

mutual
  /-- Locally nameless typing. Free names are the pair of recorded type and
  natural name; bound indices look up a distinct binder context. -/
  inductive Typed : BoundContext → Expr → Ty → Prop where
    | free : Typed Γ (.free σ x) σ
    | bound : Γ i = some σ → Typed Γ (.bound σ i) σ
    | lam : Typed (Γ.push σ) body τ → Typed Γ (.lam σ body) (.arrow σ τ)
    | head : BaseTyped Γ base f.arguments → Typed Γ (.head f base) f.result
    | marked : BaseTyped Γ base f.arguments → ExtrasTyped Γ extras →
        Typed Γ (.marked f τ base extras) τ
  inductive BaseTyped : BoundContext → Args → List Ty → Prop where
    | nil : BaseTyped Γ .nil []
    | cons : Typed Γ x σ → BaseTyped Γ xs σs →
        BaseTyped Γ (.cons x xs) (σ :: σs)
  inductive ExtrasTyped : BoundContext → Args → Prop where
    | nil : ExtrasTyped Γ .nil
    | cons : Typed Γ x σ → ExtrasTyped Γ xs → ExtrasTyped Γ (.cons x xs)
end

/-- Typed original arrow decomposition, with all supplied values living in
one outside context rather than in the consumed lambda binder contexts. -/
inductive CallTyped : BoundContext → Ty → Args → Ty → Prop where
  | nil : CallTyped Γ τ .nil τ
  | cons : Typed Γ x σ → CallTyped Γ τ xs υ →
      CallTyped Γ (.arrow σ τ) (.cons x xs) υ

/-- A local context embedding premise for the shift helper only. -/
def ShiftCompatible (amount cutoff : Nat) (Γ Δ : BoundContext) : Prop :=
  ∀ i σ, Γ i = some σ → Δ (if i < cutoff then i else i+amount) = some σ

/-- A local variable-image premise for the generic structural helper only.
The concrete finite-value-list theorem must prove this rather than assume it. -/
def SubCompatible (values : Args) (depth : Nat) (Γ Δ : BoundContext) : Prop :=
  ∀ i σ, Γ i = some σ → Typed Δ (substitute values depth (.bound σ i)) σ

end LogicLineages.PersistentMarking.Spine
