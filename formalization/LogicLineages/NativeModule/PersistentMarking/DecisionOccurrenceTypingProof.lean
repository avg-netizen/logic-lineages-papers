module

public import LogicLineages.NativeModule.PersistentMarking.DecisionObservationTargets
public import LogicLineages.NativeModule.PersistentMarking.SpineShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionOccurrenceProof
open Spine NameBridge DecisionObservations

theorem baseExtras (Γ : BoundContext) (qs : Args) (types : List Ty)
    (h : BaseTyped Γ qs types) : ExtrasTyped Γ qs := by
  cases qs with
  | nil => exact .nil
  | cons q qs => cases h with
    | cons hq hqs => exact .cons hq (baseExtras Γ qs _ hqs)
termination_by sizeOf qs

theorem typed (stack : List Ty) (t : Expr) (τ : Ty) (locals : List Ty) (q : Expr)
    (ht : Typed (BoundContext.prefix stack EmptyContext) t τ) (h : Occurs stack t locals q) :
    Typed (BoundContext.prefix locals EmptyContext) q q.type := by
  have go : ∀ υ, Typed (BoundContext.prefix stack EmptyContext) t υ →
      Typed (BoundContext.prefix locals EmptyContext) q q.type := by
    clear ht
    induction h using Occurs.rec
      (motive_2 := fun stack ts locals q _ => ExtrasTyped (BoundContext.prefix stack EmptyContext) ts →
        Typed (BoundContext.prefix locals EmptyContext) q q.type) with
    | root => intro υ hu; simpa only [SpineShiftProof.annotationExact _ _ _ hu] using hu
    | lam h ih => intro υ hu; cases hu with | lam hb => exact ih _ hb
    | head h ih => intro υ hu; cases hu with | head hb => exact ih (baseExtras _ _ _ hb)
    | markedBase h ih => intro υ hu; cases hu with | marked hb he => exact ih (baseExtras _ _ _ hb)
    | markedExtra h ih => intro υ hu; cases hu with | marked hb he => exact ih he
    | here h ih => rename_i hu; cases hu with | cons hq hqs => exact ih _ hq
    | there h ih => rename_i hu; cases hu with | cons hq hqs => exact ih hqs
  exact go τ ht
end LogicLineages.PersistentMarking.DecisionOccurrenceProof
