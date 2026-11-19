import LogicLineages.PersistentMarking.NumberedWindowRealizationShapeProof

namespace LogicLineages.PersistentMarking.NumberedWindowRealizationSubstitutionProof
open Spine NumberedWindowSyntax NumberedWindowTupleTargets NumberedWindowRealizationShapeProof

private def Paired (n : Nat) : Option Expr → Option NTerm → Prop
  | none, none => True
  | some q, some Q => Realizes n q Q
  | _, _ => False

private theorem pairedGet {n : Nat} {args : Spine.Args} {As : NArgs} (h : RealizesArgs n args As)
    (i : Nat) : Paired n (args.get i) (As.get i) := by
  induction i generalizing args As with
  | zero =>
    cases h with
    | nil => trivial
    | cons ha _ => exact ha
  | succ i ih =>
    cases h with
    | nil => trivial
    | cons _ ht => exact ih ht

private theorem substituteBound {n : Nat} {values : Spine.Args} {Values : NArgs} (hV : RealizesArgs n values Values)
    (σ : Ty) (i d : Nat) :
    Realizes n (Spine.substitute values d (.bound σ i)) (NumberedWindowSyntax.substitute Values d (.bound σ i)) := by
  by_cases hlt : i < d
  · simp only [Spine.substitute,NumberedWindowSyntax.substitute,hlt,if_true]
    exact .bound
  · have hp := pairedGet hV (i-d)
    cases hs : values.get (i-d) with
    | none =>
      cases hn : Values.get (i-d) with
      | none =>
        have hLen := (argsShape hV).1
        simp only [Spine.substitute,NumberedWindowSyntax.substitute,hlt,if_false,hs,hn,hLen]
        exact .bound
      | some Q =>
        rw [hs,hn] at hp
        exact False.elim hp
    | some q =>
      cases hn : Values.get (i-d) with
      | none =>
        rw [hs,hn] at hp
        exact False.elim hp
      | some Q =>
        rw [hs,hn] at hp
        simp only [Spine.substitute,NumberedWindowSyntax.substitute,hlt,if_false,hs,hn]
        exact shiftTerm hp d 0

theorem term {n : Nat} {values : Spine.Args} {Values : NArgs} (hV : RealizesArgs n values Values)
    {q : Expr} {Q : NTerm} (h : Realizes n q Q) :
    ∀ depth, Realizes n (Spine.substitute values depth q) (NumberedWindowSyntax.substitute Values depth Q) := by
  induction h using Realizes.rec
    (motive_2 := fun args As _ => ∀ depth, RealizesArgs n
      (Spine.substituteArgs values depth args) (NumberedWindowSyntax.substituteArgs Values depth As)) with
  | free => intro depth; exact .free
  | bound => intro depth; exact substituteBound hV _ _ depth
  | lam _ ih => intro depth; exact .lam (ih (depth+1))
  | ordinary _ ih => intro depth; exact .ordinary (ih depth)
  | marked hk _ _ ihb ihe => intro depth; exact .marked hk (ihb depth) (ihe depth)
  | nil => intros; exact .nil
  | cons _ _ ih iht => rename_i depth; exact .cons (ih depth) (iht depth)

theorem args {n : Nat} {values : Spine.Args} {Values : NArgs} (hV : RealizesArgs n values Values)
    {bs : Spine.Args} {Bs : NArgs} (h : RealizesArgs n bs Bs) (depth : Nat) :
    RealizesArgs n (Spine.substituteArgs values depth bs) (NumberedWindowSyntax.substituteArgs Values depth Bs) := by
  cases h with
  | nil => exact .nil
  | cons h ht => exact .cons (term hV h depth) (args hV ht depth)
termination_by sizeOf bs

end LogicLineages.PersistentMarking.NumberedWindowRealizationSubstitutionProof
