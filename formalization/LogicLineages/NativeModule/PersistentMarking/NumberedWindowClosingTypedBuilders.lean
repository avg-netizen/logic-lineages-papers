module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosing

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingTypedBuilders
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing
open NameBridge (Name)

def TermGoal (n : Name) (C : Spine.BoundContext) (q : NTerm) (τ : Ty) : Prop :=
  ∀ d D, CloseCompatible n d C D → Typed D (closeAt n d q) τ

def BaseGoal (n : Name) (C : Spine.BoundContext) (As : NArgs) (types : List Ty) : Prop :=
  ∀ d D, CloseCompatible n d C D → BaseTyped D (closeArgsAt n d As) types

def ExtrasGoal (n : Name) (C : Spine.BoundContext) (As : NArgs) : Prop :=
  ∀ d D, CloseCompatible n d C D → ExtrasTyped D (closeArgsAt n d As)

theorem push {n d C D} (h : CloseCompatible n d C D) (σ : Ty) :
    CloseCompatible n (d+1) (C.push σ) (D.push σ) := by
  refine ⟨h.1,?_⟩
  intro i τ hi
  cases i with
  | zero => exact hi
  | succ i => exact h.2 i τ hi

theorem bFree (n : Name) (C : Spine.BoundContext) (σ : Ty) (x : Nat) :
    TermGoal n C (.free σ x) σ := by
  intro d D h
  by_cases he : (σ,x) = n
  · simp only [closeAt,he,if_true]
    exact .bound (by rw [← he] at h; exact h.1)
  · simp only [closeAt,he,if_false]
    exact .free

theorem bBound (n : Name) (C : Spine.BoundContext) (i : Nat) (σ : Ty)
    (hi : C i = some σ) : TermGoal n C (.bound σ i) σ :=
  fun _ _ h => .bound (h.2 i σ hi)

theorem bLam (n : Name) (C : Spine.BoundContext) (σ : Ty) (body : NTerm) (τ : Ty)
    (_ : Typed (C.push σ) body τ) (ih : TermGoal n (C.push σ) body τ) :
    TermGoal n C (.lam σ body) (.arrow σ τ) :=
  fun d D h => .lam (ih (d+1) (D.push σ) (push h σ))

theorem bBottom (n : Name) (C : Spine.BoundContext) (τ : Ty) :
    TermGoal n C (.bottom τ) τ := fun _ _ _ => .bottom

theorem bOrdinary (n : Name) (C : Spine.BoundContext) (bs : NArgs) (f : Head)
    (_ : BaseTyped C bs f.arguments) (ih : BaseGoal n C bs f.arguments) :
    TermGoal n C (.ordinary f bs) f.result :=
  fun d D h => .ordinary (ih d D h)

theorem bNumbered (n : Name) (C : Spine.BoundContext) (bs : NArgs) (f : Head)
    (es : NArgs) (τ : Ty) (k : Nat)
    (_ : BaseTyped C bs f.arguments) (_ : ExtrasTyped C es)
    (hb : BaseGoal n C bs f.arguments) (he : ExtrasGoal n C es) :
    TermGoal n C (.numbered f τ k bs es) τ :=
  fun d D h => .numbered (hb d D h) (he d D h)

theorem bAuxApp (n : Name) (C : Spine.BoundContext) (q : NTerm) (σ τ : Ty)
    (a : NTerm) (_ : Typed C q (.arrow σ τ)) (_ : Typed C a σ)
    (hq : TermGoal n C q (.arrow σ τ)) (ha : TermGoal n C a σ) :
    TermGoal n C (.auxApp σ τ q a) τ :=
  fun d D h => .auxApp (hq d D h) (ha d D h)

theorem bBaseNil (n : Name) (C : Spine.BoundContext) :
    BaseGoal n C .nil [] := fun _ _ _ => .nil

theorem bBaseCons (n : Name) (C : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (qs : NArgs) (types : List Ty) (_ : Typed C q τ) (_ : BaseTyped C qs types)
    (hq : TermGoal n C q τ) (hqs : BaseGoal n C qs types) :
    BaseGoal n C (.cons q qs) (τ::types) :=
  fun d D h => .cons (hq d D h) (hqs d D h)

theorem bExtrasNil (n : Name) (C : Spine.BoundContext) :
    ExtrasGoal n C .nil := fun _ _ _ => .nil

theorem bExtrasCons (n : Name) (C : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (qs : NArgs) (_ : Typed C q τ) (_ : ExtrasTyped C qs)
    (hq : TermGoal n C q τ) (hqs : ExtrasGoal n C qs) :
    ExtrasGoal n C (.cons q qs) :=
  fun d D h => .cons (hq d D h) (hqs d D h)

end LogicLineages.PersistentMarking.NumberedWindowClosingTypedBuilders
