module
public import LogicLineages.ControlSensitivityCurrent.CurrentReserveDeterminacyProof
public import LogicLineages.ControlSensitivityCurrent.PolicyGadgetProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentReserve

open LogicLineages.OrdinalComparison.Source
open ActiveScalarAnnotation AdmissibleSum

private theorem shapeThree {Γ : List Ty} (n : Nat) (s : Shape n) (hn : n=3)
    (a b c : OrdinalExpression Γ) :
    expand s (fun j => if j.val = 0 then a else if j.val = 1 then b else c) =
        .add (.add a b) c ∨
    expand s (fun j => if j.val = 0 then a else if j.val = 1 then b else c) =
        .add a (.add b c) := by
  cases s with
  | leaf => omega
  | @join l r u v =>
    have hl := PolicyGadget.smallShapes.1 l u
    have hr := PolicyGadget.smallShapes.1 r v
    by_cases he : l=1
    · have he' : r=2 := by omega
      subst l
      subst r
      rw [PolicyGadget.smallShapes.2.1 u,PolicyGadget.smallShapes.2.2 v]
      exact Or.inr rfl
    · have hl' : l=2 := by omega
      have hr' : r=1 := by omega
      subst l
      subst r
      rw [PolicyGadget.smallShapes.2.2 u,PolicyGadget.smallShapes.2.1 v]
      exact Or.inl rfl

theorem activeAddCases (p : Policy) {Γ : List Ty} (a b c : OrdinalExpression Γ) :
    AdmissiblePartial.three p .activeAdd a b c = .add (.add a b) c ∨
      AdmissiblePartial.three p .activeAdd a b c = .add a (.add b c) :=
  shapeThree 3 (p.shape .activeAdd 2) rfl a b c

/-- The real selected policy association preserves the concatenated
occurrence list. If the right two operands are both F-free, their cluster
is one free stop, so we assert only nondecrease. -/
theorem accountThree (p : Policy) (f : Nat → Nat) {k Γ}
    (a b : OrdinalExpression (Ty.curriedGround (k+1) :: Γ))
    (xs ys : List (Carrier p)) (c d : Nat)
    (ha : Account p f a xs c) (hb : Account p f b ys d)
    (hact : Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) a ∨
      Active (.here : Variable (Ty.curriedGround (k+1) :: Γ) _) b) :
    ∃ e : Nat, Account p f (AdmissiblePartial.three p .activeAdd a b .one) (xs++ys) e ∧ c+d+1 ≤ e := by
  classical
  let F : Variable (Ty.curriedGround (k+1) :: Γ) (Ty.curriedGround (k+1)) := .here
  have hOne : Account p f (.one : OrdinalExpression (Ty.curriedGround (k+1) :: Γ)) [] 1 :=
    .free (inactiveOne F)
  rcases activeAddCases p a b .one with hL | hR
  · rw [hL]
    have hAB : Active F (.add a b) := (activeAdd F a b).2 hact
    have hOuter : Active F (.add (.add a b) .one) := (activeAdd F _ _).2 (Or.inl hAB)
    have out := AccountWith.add hOuter (AccountWith.add hAB ha hb) hOne
    exact ⟨c+d+1+1+1,by simpa only [List.append_nil] using out,by omega⟩
  · rw [hR]
    by_cases hB : Active F b
    · have hInner : Active F (.add b .one) := (activeAdd F _ _).2 (Or.inl hB)
      have hOuter : Active F (.add a (.add b .one)) := (activeAdd F _ _).2 (Or.inr hInner)
      have out := AccountWith.add hOuter ha (AccountWith.add hInner hb hOne)
      exact ⟨c+(d+1+1)+1,by simpa only [List.append_nil] using out,by omega⟩
    · obtain ⟨rfl,rfl⟩ := inactiveData hb hB
      have hA : Active F a := hact.resolve_right hB
      have hInner : ¬ Active F (.add b .one) := fun h => ((activeAdd F _ _).1 h).elim hB (inactiveOne F)
      have hOuter : Active F (.add a (.add b .one)) := (activeAdd F _ _).2 (Or.inl hA)
      exact ⟨c+1+1,AccountWith.add hOuter ha (.free hInner),le_rfl⟩

end LogicLineages.ControlSensitivityCurrent.CurrentReserve
