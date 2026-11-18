module
public import LogicLineages.StandardControlCurrent.PolicyPartialTargets
public import LogicLineages.StandardControlCurrent.PolicyShapeSyntaxProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyPartialMergeProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

theorem three (p : Policy) (site : MacroSite) {Γ : List Ty}
    (a b c : OrdinalExpression Γ) :
    PolicyShape.macroCode p (PolicyShape.siteCode site) 2 [typedCode a,typedCode b,typedCode c] =
      some (typedCode (AdmissiblePartial.three p site a b c)) := by
  simpa [AdmissiblePartial.three, List.ofFn_succ] using
    PolicyShapeSyntaxProof.literal.1 p site Γ 2
      (fun i => if i.val=0 then a else if i.val=1 then b else c)

theorem twice (p : Policy) {Γ : List Ty} (a : OrdinalExpression Γ) :
    PolicyShape.macroCode p (PolicyShape.siteCode .positiveRepeat) 1 [typedCode a,typedCode a] =
      some (typedCode (AdmissiblePartial.twice p a)) := by
  simpa [AdmissiblePartial.twice, List.ofFn_succ] using
    PolicyShapeSyntaxProof.literal.1 p .positiveRepeat Γ 1 (fun _ => a)

theorem coordinate (p : Policy) {Γ : List Ty} (tag : Nat) (a b : OrdinalExpression Γ) :
    PolicyPartial.mergeCoordinate p tag (typedCode a) (typedCode b) =
      some (typedCode (if tag=5 then
        AdmissiblePartial.three p .activeExp (AdmissiblePartial.twice p a) b .one
        else AdmissiblePartial.three p .activeAdd a b .one)) := by
  by_cases h : tag=5
  · simp only [PolicyPartial.mergeCoordinate,h,if_true,twice,bind,pure,Option.bind_some]
    exact three p .activeExp _ _ _
  · simp only [PolicyPartial.mergeCoordinate,h,if_false,bind,pure,Option.bind_some]
    exact three p .activeAdd _ _ _

theorem calibration : PolicyPartialTargets.CoordinateCalibration := by
  intro p Γ a b
  exact ⟨by simpa using coordinate p 4 a b, by simpa using coordinate p 5 a b⟩

private theorem collect (step : Nat → Option Nat) (out : Nat → Nat)
    (xs : List Nat) (acc : List Nat) (h : ∀ j ∈ xs, step j=some (out j)) :
    xs.foldl (fun acc j => do let ys ← acc; let y ← step j; pure (ys++[y])) (some acc) =
      some (acc ++ xs.map out) := by
  induction xs generalizing acc with
  | nil => simp
  | cons j js ih =>
    simp only [List.foldl_cons,h j (by simp),bind,pure,Option.bind_some]
    rw [ih _ (fun k hk => h k (by simp [hk]))]
    simp

theorem merge_codes (p : Policy) {Γ : List Ty} {σ : Ty} (tag : Nat)
    (a b : OrdinalPartialVector Γ σ) :
    PolicyPartial.mergeCode p σ.level tag
      (List.ofFn (fun j => typedCode (a j))) (List.ofFn (fun j => typedCode (b j))) =
      some (List.ofFn (fun j => typedCode (if tag=5 then
        AdmissiblePartial.three p .activeExp (AdmissiblePartial.twice p (a j)) (b j) .one
        else AdmissiblePartial.three p .activeAdd (a j) (b j) .one))) := by
  let out : Nat → Nat := fun j => if h : j<σ.level+2 then
    typedCode (if tag=5 then
      AdmissiblePartial.three p .activeExp (AdmissiblePartial.twice p (a ⟨j,h⟩)) (b ⟨j,h⟩) .one
      else AdmissiblePartial.three p .activeAdd (a ⟨j,h⟩) (b ⟨j,h⟩) .one) else 0
  unfold PolicyPartial.mergeCode
  rw [collect _ out _ []]
  · congr 1
    apply List.ext_getElem
    · simp
    · intro j hj hk
      have hj' : j<σ.level+2 := by simpa using hj
      simp [out,hj']
  · intro j hj
    have hj' : j<σ.level+2 := List.mem_range.mp hj
    simpa [out,hj',List.getD_eq_getElem?_getD,List.getElem?_ofFn] using
      coordinate p tag (a ⟨j,hj'⟩) (b ⟨j,hj'⟩)
end LogicLineages.StandardControlCurrent.PolicyPartialMergeProof
