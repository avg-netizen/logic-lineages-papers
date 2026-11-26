module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingAbsThinBuilders

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingAbsThinCore
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowClosingAbsThinBuilders
open NameBridge (Name)

theorem term (n : Name) {C q τ} (ht : Typed C q τ) : TermGoal n C q :=
  Typed.rec
    (motive_1 := fun C q _ _ => TermGoal n C q)
    (motive_2 := fun C qs _ _ => ArgsGoal n C qs)
    (motive_3 := fun C qs _ => ArgsGoal n C qs)
    (@bFree n)
    (by intro C σ i hi; exact @bBound n C i σ hi)
    (by intro _ _ _ _ h ih; exact @bLam n _ _ _ _ h ih)
    (@bBottom n)
    (by intro _ _ _ h ih; exact @bOrdinary n _ _ _ h ih)
    (by intro _ _ _ _ _ _ hb he ib ie; exact @bNumbered n _ _ _ _ _ _ hb he ib ie)
    (by intro _ _ _ _ _ hq ha iq ia; exact @bAuxApp n _ _ _ _ _ hq ha iq ia)
    (@bNil n)
    (by intro _ _ _ _ _ hq hs iq is; exact @bBaseCons n _ _ _ _ _ hq hs iq is)
    (@bNil n)
    (by intro _ _ _ _ hq hs iq is; exact @bExtrasCons n _ _ _ _ hq hs iq is)
    ht

end LogicLineages.PersistentMarking.NumberedWindowClosingAbsThinCore
