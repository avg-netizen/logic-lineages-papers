module

public import LogicLineages.NativeModule.PersistentMarking.RankedRestrictionSyntaxProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RankedRestrictionEqualityProof
open Spine RankedRestrictionTargets RankedRestrictionSyntaxProof

def EqualGoal (S : Signature) (q t : Expr) : Prop :=
  RankedTerm S q → RankedTerm S t → Weak S q t

def MatchGoal (S : Signature) (qs ts : Args) : Prop :=
  ArgsTerm S qs → ArgsTerm S ts → Matching S qs ts

theorem var (S : Signature) (x : Nat) : EqualGoal S (.free .ground x) (.free .ground x) :=
  fun _ _ => .var

theorem head (S : Signature) (f : Head) (bs ts : Args) (ih : MatchGoal S bs ts) :
    EqualGoal S (.head f bs) (.head f ts) := by
  intro hs ht
  have he : f.result = .ground := annotation _ hs.2
  obtain ⟨r,hr⟩ := hs.1.2.1
  exact .funHead (he.symm ▸ hs.1) (he.symm ▸ ht.1) ⟨r,hr,hr⟩ rfl
    (ih (baseAt S f bs hs) (baseAt S f ts ht))

theorem nil (S : Signature) : MatchGoal S .nil .nil :=
  fun _ _ => .nil

theorem cons (S : Signature) (q t : Expr) (qs ts rest : Args) (hr : Remove ts t rest)
    (ih : EqualGoal S q t) (ih' : MatchGoal S qs rest) : MatchGoal S (.cons q qs) ts := by
  intro hS hT
  obtain ⟨ht,hT'⟩ := RankedRestrictionSyntaxProof.remove S hr hT
  exact .cons hr (ih (hS 0 q .here) ht) (ih' (fun i u ha => hS (i+1) u (.there ha)) hT')

theorem equal (S : Signature) (q t : Expr) (h : Equal q t) : EqualGoal S q t := by
  refine Equal.rec (motive_1 := fun q t _ => EqualGoal S q t)
    (motive_2 := fun qs ts _ => MatchGoal S qs ts)
    ?_ ?_ ?_ ?_ h
  · intros
    exact var S _
  · intros
    exact head S _ _ _ (by assumption)
  · exact nil S
  · intros
    rename_i hr hq hrest ih ih'
    exact cons S _ _ _ _ _ hr ih ih'

theorem matching (S : Signature) (qs ts : Args) (h : EqMatch qs ts) : MatchGoal S qs ts := by
  cases h with
  | nil => exact nil S
  | cons hr he hm => exact cons S _ _ _ _ _ hr (equal S _ _ he) (matching S _ _ hm)
termination_by sizeOf qs

end LogicLineages.PersistentMarking.RankedRestrictionEqualityProof
