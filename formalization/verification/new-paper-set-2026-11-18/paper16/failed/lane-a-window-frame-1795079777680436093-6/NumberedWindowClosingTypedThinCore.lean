import LogicLineages.PersistentMarking.NumberedWindowClosingTypedBuilders

namespace LogicLineages.PersistentMarking.NumberedWindowClosingTypedThinCore
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowClosing
open NumberedWindowClosingTypedBuilders
open NameBridge (Name)

theorem term (n : Name) (d : Nat) (C D : Spine.BoundContext) (q : NTerm) (τ : Ty)
    (h : Typed C q τ) (hc : CloseCompatible n d C D) : Typed D (closeAt n d q) τ :=
  (Typed.rec
    (motive_1 := fun C q τ _ => TermGoal n C q τ)
    (motive_2 := fun C qs types _ => BaseGoal n C qs types)
    (motive_3 := fun C qs _ => ExtrasGoal n C qs)
    (@bFree n) (@bBound n) (@bLam n) (@bBottom n) (@bOrdinary n) (@bNumbered n) (@bAuxApp n)
    (@bBaseNil n) (@bBaseCons n) (@bExtrasNil n) (@bExtrasCons n) h) d D hc

theorem base (n : Name) (d : Nat) (C D : Spine.BoundContext) (As : NArgs) (types : List Ty)
    (h : BaseTyped C As types) (hc : CloseCompatible n d C D) :
    BaseTyped D (closeArgsAt n d As) types :=
  (BaseTyped.rec
    (motive_1 := fun C q τ _ => TermGoal n C q τ)
    (motive_2 := fun C qs types _ => BaseGoal n C qs types)
    (motive_3 := fun C qs _ => ExtrasGoal n C qs)
    (@bFree n) (@bBound n) (@bLam n) (@bBottom n) (@bOrdinary n) (@bNumbered n) (@bAuxApp n)
    (@bBaseNil n) (@bBaseCons n) (@bExtrasNil n) (@bExtrasCons n) h) d D hc

theorem extras (n : Name) (d : Nat) (C D : Spine.BoundContext) (As : NArgs)
    (h : ExtrasTyped C As) (hc : CloseCompatible n d C D) : ExtrasTyped D (closeArgsAt n d As) :=
  (ExtrasTyped.rec
    (motive_1 := fun C q τ _ => TermGoal n C q τ)
    (motive_2 := fun C qs types _ => BaseGoal n C qs types)
    (motive_3 := fun C qs _ => ExtrasGoal n C qs)
    (@bFree n) (@bBound n) (@bLam n) (@bBottom n) (@bOrdinary n) (@bNumbered n) (@bAuxApp n)
    (@bBaseNil n) (@bBaseCons n) (@bExtrasNil n) (@bExtrasCons n) h) d D hc

end LogicLineages.PersistentMarking.NumberedWindowClosingTypedThinCore
