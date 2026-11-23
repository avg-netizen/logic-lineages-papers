module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowRealizationShapeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowRealizationTypingProof
open Spine NumberedWindowSyntax NumberedWindowTupleTargets

def ArgsTyping (args : Spine.Args) (As : NArgs) : Prop :=
  (∀ C types, Spine.BaseTyped C args types → NumberedWindowDomain.BaseTyped C As types) ∧
  (∀ C, Spine.ExtrasTyped C args → NumberedWindowDomain.ExtrasTyped C As)

theorem typed {n : Nat} {q : Expr} {Q : NTerm} (h : Realizes n q Q) :
    ∀ C τ, Spine.Typed C q τ → NumberedWindowDomain.Typed C Q τ := by
  induction h using Realizes.rec
    (motive_2 := fun args As _ => ArgsTyping args As) with
  | free =>
    intro C τ h
    cases h
    exact .free
  | bound =>
    intro C τ h
    cases h with
    | bound hi => exact .bound hi
  | lam _ ih =>
    intro C τ h
    cases h with
    | lam hb => exact .lam (ih _ _ hb)
  | ordinary _ ih =>
    intro C τ h
    cases h with
    | head hb => exact .ordinary (ih.1 _ _ hb)
  | marked _ _ _ ihb ihe =>
    intro C τ h
    cases h with
    | marked hb he => exact .numbered (ihb.1 _ _ hb) (ihe.2 _ he)
  | nil =>
    exact ⟨fun _ _ h => by cases h; exact .nil, fun _ _ => .nil⟩
  | cons _ _ ih iht =>
    constructor
    · intro C types h
      cases h with
      | cons ha ht => exact .cons (ih _ _ ha) (iht.1 _ _ ht)
    · intro C h
      cases h with
      | cons ha ht => exact .cons (ih _ _ ha) (iht.2 _ ht)

theorem typedArgs {n : Nat} {args : Spine.Args} {As : NArgs} (h : RealizesArgs n args As) :
    ArgsTyping args As := by
  cases h with
  | nil => exact ⟨fun _ _ h => by cases h; exact .nil, fun _ _ => .nil⟩
  | cons h ht =>
    have ih := typedArgs ht
    constructor
    · intro C types hp
      cases hp with
      | cons ha hta => exact .cons (typed h _ _ ha) (ih.1 _ _ hta)
    · intro C hp
      cases hp with
      | cons ha hta => exact .cons (typed h _ _ ha) (ih.2 _ hta)
termination_by sizeOf args

end LogicLineages.PersistentMarking.NumberedWindowRealizationTypingProof
