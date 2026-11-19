import LogicLineages.PersistentMarking.NumberedWindowClosingFreshProof
import LogicLineages.PersistentMarking.NumberedWindowClosingScopeProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingAbsThinBuilders
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing
open NumberedWindowClosingFreshProof (Fresh FreshArgs)
open NumberedWindowClosingScopeProof (Below belowPush)
open NameBridge (Name)

def ScopeAt (C : Spine.BoundContext) (d : Nat) (σ : Ty) : Prop :=
  C d = some σ ∧ Below C (d+1)

private theorem push {C d σ} (h : ScopeAt C d σ) (τ : Ty) : ScopeAt (C.push τ) (d+1) σ :=
  ⟨h.1,belowPush h.2 τ⟩

def TermGoal (n : Name) (C : Spine.BoundContext) (q : NTerm) : Prop :=
  ∀ d, Fresh n q → ScopeAt C d n.1 →
    closeAt n d (substitute (.cons (.free n.1 n.2) .nil) d q) = q

def ArgsGoal (n : Name) (C : Spine.BoundContext) (As : NArgs) : Prop :=
  ∀ d, FreshArgs n As → ScopeAt C d n.1 →
    closeArgsAt n d (substituteArgs (.cons (.free n.1 n.2) .nil) d As) = As

theorem bFree (n : Name) (C : Spine.BoundContext) (σ : Ty) (x : Nat) :
    TermGoal n C (.free σ x) := by
  intro d hf _
  change (σ,x) ≠ n at hf
  simp only [substitute,closeAt,hf,if_false]

theorem bBound (n : Name) (C : Spine.BoundContext) (i : Nat) (τ : Ty)
    (hi : C i = some τ) : TermGoal n C (.bound τ i) := by
  intro d _ h
  by_cases hl : i < d
  · simp only [substitute,hl,if_true,closeAt]
  · have he : i = d := by
      have hi' := h.2 i τ hi
      omega
    subst i
    have hτ : τ = n.1 := Option.some.inj (hi.symm.trans h.1)
    subst τ
    simp [substitute,shift,NArgs.get,closeAt]

theorem bLam (n : Name) (C : Spine.BoundContext) (σ : Ty) (body : NTerm) (τ : Ty)
    (_ : Typed (C.push σ) body τ) (ih : TermGoal n (C.push σ) body) :
    TermGoal n C (.lam σ body) :=
  fun d hf hs => congrArg (NTerm.lam σ) (ih (d+1) hf (push hs σ))

theorem bBottom (n : Name) (C : Spine.BoundContext) (τ : Ty) :
    TermGoal n C (.bottom τ) := fun _ _ _ => rfl

theorem bOrdinary (n : Name) (C : Spine.BoundContext) (bs : NArgs) (f : Head)
    (_ : BaseTyped C bs f.arguments) (ih : ArgsGoal n C bs) :
    TermGoal n C (.ordinary f bs) :=
  fun d hf hs => congrArg (NTerm.ordinary f) (ih d hf hs)

theorem bNumbered (n : Name) (C : Spine.BoundContext) (bs : NArgs) (f : Head)
    (es : NArgs) (τ : Ty) (k : Nat)
    (_ : BaseTyped C bs f.arguments) (_ : ExtrasTyped C es)
    (hb : ArgsGoal n C bs) (he : ArgsGoal n C es) :
    TermGoal n C (.numbered f τ k bs es) := by
  intro d hf hs
  simp only [substitute,closeAt,hb d hf.1 hs,he d hf.2 hs]

theorem bAuxApp (n : Name) (C : Spine.BoundContext) (q : NTerm) (σ τ : Ty)
    (a : NTerm) (_ : Typed C q (.arrow σ τ)) (_ : Typed C a σ)
    (hq : TermGoal n C q) (ha : TermGoal n C a) :
    TermGoal n C (.auxApp σ τ q a) := by
  intro d hf hs
  simp only [substitute,closeAt,hq d hf.1 hs,ha d hf.2 hs]

theorem bNil (n : Name) (C : Spine.BoundContext) :
    ArgsGoal n C .nil := fun _ _ _ => rfl

theorem bBaseCons (n : Name) (C : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (qs : NArgs) (types : List Ty) (_ : Typed C q τ) (_ : BaseTyped C qs types)
    (hq : TermGoal n C q) (hqs : ArgsGoal n C qs) :
    ArgsGoal n C (.cons q qs) := by
  intro d hf hs
  simp only [substituteArgs,closeArgsAt,hq d hf.1 hs,hqs d hf.2 hs]

theorem bExtrasCons (n : Name) (C : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (qs : NArgs) (_ : Typed C q τ) (_ : ExtrasTyped C qs)
    (hq : TermGoal n C q) (hqs : ArgsGoal n C qs) :
    ArgsGoal n C (.cons q qs) := by
  intro d hf hs
  simp only [substituteArgs,closeArgsAt,hq d hf.1 hs,hqs d hf.2 hs]

end LogicLineages.PersistentMarking.NumberedWindowClosingAbsThinBuilders
