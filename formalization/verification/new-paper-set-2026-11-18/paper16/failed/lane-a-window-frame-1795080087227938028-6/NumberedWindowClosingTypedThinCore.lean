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
    (@bFree n)
    (by intro C σ i hi; exact @bBound n C i σ hi)
    (by intro _ _ _ _ ht ih; exact @bLam n _ _ _ _ ht ih)
    (@bBottom n)
    (by intro _ _ _ hb ih; exact @bOrdinary n _ _ _ hb ih)
    (by intro _ _ _ _ _ _ hb he ib ie; exact @bNumbered n _ _ _ _ _ _ hb he ib ie)
    (by intro _ _ _ _ _ hq ha iq ia; exact @bAuxApp n _ _ _ _ _ hq ha iq ia)
    (@bBaseNil n)
    (by intro _ _ _ _ _ hq hs iq is; exact @bBaseCons n _ _ _ _ _ hq hs iq is)
    (@bExtrasNil n)
    (by intro _ _ _ _ hq hs iq is; exact @bExtrasCons n _ _ _ _ hq hs iq is)
    h) d D hc

theorem base (n : Name) (d : Nat) (C D : Spine.BoundContext) (As : NArgs) (types : List Ty)
    (h : BaseTyped C As types) (hc : CloseCompatible n d C D) :
    BaseTyped D (closeArgsAt n d As) types :=
  (BaseTyped.rec
    (motive_1 := fun C q τ _ => TermGoal n C q τ)
    (motive_2 := fun C qs types _ => BaseGoal n C qs types)
    (motive_3 := fun C qs _ => ExtrasGoal n C qs)
    (@bFree n)
    (by intro C σ i hi; exact @bBound n C i σ hi)
    (by intro _ _ _ _ ht ih; exact @bLam n _ _ _ _ ht ih)
    (@bBottom n)
    (by intro _ _ _ hb ih; exact @bOrdinary n _ _ _ hb ih)
    (by intro _ _ _ _ _ _ hb he ib ie; exact @bNumbered n _ _ _ _ _ _ hb he ib ie)
    (by intro _ _ _ _ _ hq ha iq ia; exact @bAuxApp n _ _ _ _ _ hq ha iq ia)
    (@bBaseNil n)
    (by intro _ _ _ _ _ hq hs iq is; exact @bBaseCons n _ _ _ _ _ hq hs iq is)
    (@bExtrasNil n)
    (by intro _ _ _ _ hq hs iq is; exact @bExtrasCons n _ _ _ _ hq hs iq is)
    h) d D hc

theorem extras (n : Name) (d : Nat) (C D : Spine.BoundContext) (As : NArgs)
    (h : ExtrasTyped C As) (hc : CloseCompatible n d C D) : ExtrasTyped D (closeArgsAt n d As) :=
  (ExtrasTyped.rec
    (motive_1 := fun C q τ _ => TermGoal n C q τ)
    (motive_2 := fun C qs types _ => BaseGoal n C qs types)
    (motive_3 := fun C qs _ => ExtrasGoal n C qs)
    (@bFree n)
    (by intro C σ i hi; exact @bBound n C i σ hi)
    (by intro _ _ _ _ ht ih; exact @bLam n _ _ _ _ ht ih)
    (@bBottom n)
    (by intro _ _ _ hb ih; exact @bOrdinary n _ _ _ hb ih)
    (by intro _ _ _ _ _ _ hb he ib ie; exact @bNumbered n _ _ _ _ _ _ hb he ib ie)
    (by intro _ _ _ _ _ hq ha iq ia; exact @bAuxApp n _ _ _ _ _ hq ha iq ia)
    (@bBaseNil n)
    (by intro _ _ _ _ _ hq hs iq is; exact @bBaseCons n _ _ _ _ _ hq hs iq is)
    (@bExtrasNil n)
    (by intro _ _ _ _ hq hs iq is; exact @bExtrasCons n _ _ _ _ hq hs iq is)
    h) d D hc

end LogicLineages.PersistentMarking.NumberedWindowClosingTypedThinCore
