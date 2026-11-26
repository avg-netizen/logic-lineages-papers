module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPrimaryCoverPermProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverBoundsProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPrimary
open NumberedWindowPrimaryCoverSyntax NumberedWindowPrimaryCoverTargets
open NumberedWindowPrimaryCoverPermProof (perm)

theorem term {S K C τ Q R} (h : Primary S K C τ Q R) : termBounds Q = termBounds R := by
  induction h using Primary.rec
    (motive_2 := fun _ _ qs rs _ => argsBounds qs = argsBounds rs) with
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ e d => exact e.trans d
  | ordinary _ _ _ _ _ _ hperm => simp only [termBounds,perm hperm]
  | numbered _ _ _ _ _ _ hperm => simp only [termBounds,perm hperm]
  | lam _ ih => simp only [termBounds,ih]
  | appFunction _ _ ih => simp only [termBounds,ih]
  | appArgument _ _ ih => simp only [termBounds,ih]
  | ordinaryArguments _ ih => simp only [termBounds,ih]
  | numberedBase _ _ ih => simp only [termBounds,ih]
  | numberedExtras _ _ ih => simp only [termBounds,ih]
  | nil => rfl
  | cons _ _ e d => simp only [argsBounds,e,d]

theorem args {S K C types qs rs} (h : OrderedPrimary S K C types qs rs) :
    argsBounds qs = argsBounds rs := by
  have hL := term (Primary.numberedExtras
    (f := Head.zero) (τ := Ty.ground) (k := 0) (bs := NArgs.nil) BaseTyped.nil h)
  have hn : (argsBounds qs).nodes = (argsBounds rs).nodes := by
    have e := congrArg Bounds.nodes hL
    simpa only [termBounds,argsBounds,Nat.zero_add,Nat.add_right_cancel_iff] using e
  have hm : (argsBounds qs).numeral = (argsBounds rs).numeral := by
    have e := congrArg Bounds.numeral hL
    simpa only [termBounds,argsBounds,Nat.zero_max] using e
  cases eqQ : argsBounds qs
  cases eqR : argsBounds rs
  simp only [eqQ,eqR] at hn hm
  simp only [Bounds.mk.injEq]
  exact ⟨hn,hm⟩

theorem both : PrimaryBounds :=
  ⟨fun _ _ _ _ _ _ h => term h,fun _ _ _ _ _ _ h => args h⟩

end LogicLineages.PersistentMarking.NumberedWindowPrimaryCoverBoundsProof
