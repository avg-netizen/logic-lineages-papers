module
public import LogicLineages.StandardControlCurrent.PolicyIndexedMergeTargets
import LogicLineages.StandardControlCurrent.PolicyIndexedShapeProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedMerge
open PolicyIndexedShape (policyIndexedShapePartrec exactPolicyIndexedShape)

private theorem onSome {A B C : Type} [Primcodable A] [Primcodable B] [Inhabited B] [Primcodable C]
    {branch : A → B → Part (Option C)} (h : Partrec₂ branch) :
    Partrec (fun x : A × Option B => match x.2 with
      | none => Part.some none
      | some b => branch x.1 b) := by
  let flag (x : A × Option B) := bif x.2.isSome then 1 else 0
  have hf : Computable flag := Computable.cond
    (Primrec.option_isSome.to_comp.comp Computable.snd) (Computable.const 1) (Computable.const 0)
  have hd : Computable (fun x : A × Option B => x.2.getD default) :=
    Computable.option_getD Computable.snd (Computable.const default)
  have hk : Partrec₂ (fun (x : A × Option B) (_ : Nat) =>
      branch x.1 (x.2.getD default)) :=
    (h.comp (Computable.fst.comp Computable.fst) (hd.comp Computable.fst)).to₂
  exact (Partrec.nat_casesOn_right hf (Computable.const none) hk).of_eq
    (fun ⟨a,b⟩ => by cases b <;> rfl)

private theorem operandPartrec : Partrec firstOperand := by
  have ht : Computable (fun x : CoordinateArgs => x.2.1) := Computable.fst.comp Computable.snd
  have ha : Computable (fun x : CoordinateArgs => x.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  let flag (x : CoordinateArgs) := if x.2.1 = 5 then 1 else 0
  have hf : Computable flag :=
    (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 5))
      (Primrec.const 1) (Primrec.const 0)).to_comp
  let T := CoordinateArgs × Nat
  have ha' : Computable (fun x : T => x.1.2.2.1) := ha.comp Computable.fst
  have hs : Computable (fun x : T =>
      (x.1.1,PolicyShape.siteCode .positiveRepeat,1,[x.1.2.2.1,x.1.2.2.1])) :=
    (Computable.fst.comp Computable.fst).pair
      ((Computable.const (PolicyShape.siteCode .positiveRepeat)).pair
        ((Computable.const 1).pair
          (Primrec.list_cons.to_comp.comp ha'
            (Primrec.list_cons.to_comp.comp ha' (Computable.const [])))))
  exact (Partrec.nat_casesOn_right hf (Computable.option_some.comp ha)
    (policyIndexedShapePartrec.comp hs).to₂).of_eq (fun x => by
      by_cases h : x.2.1 = 5 <;> simp [flag,firstOperand,h])

private theorem remainingPartrec :
    Partrec₂ (fun (x : CoordinateArgs) (a : Nat) => PolicyIndexedShape.macroCode
      (x.1,PolicyShape.siteCode (if x.2.1 = 5 then .activeExp else .activeAdd),2,[a,x.2.2.2,1])) := by
  let Q := CoordinateArgs × Nat
  have ht : Primrec (fun q : Q => q.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hsite : Primrec (fun q : Q =>
      PolicyShape.siteCode (if q.1.2.1 = 5 then .activeExp else .activeAdd)) :=
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 5))
      (Primrec.const (PolicyShape.siteCode .activeExp))
      (Primrec.const (PolicyShape.siteCode .activeAdd))).of_eq (fun q => by split <;> rfl)
  have hb : Computable (fun q : Q => q.1.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
  have harg : Computable (fun q : Q =>
      (q.1.1,PolicyShape.siteCode (if q.1.2.1 = 5 then .activeExp else .activeAdd),2,[q.2,q.1.2.2.2,1])) :=
    (Computable.fst.comp Computable.fst).pair
      (hsite.to_comp.pair ((Computable.const 2).pair
        (Primrec.list_cons.to_comp.comp Computable.snd
          (Primrec.list_cons.to_comp.comp hb (Computable.const [1])))))
  exact (policyIndexedShapePartrec.comp harg).to₂


theorem coordinateExact : ExactCoordinate := by
  intro c p hc tag a b
  have hfirst : firstOperand (c,tag,a,b) = Part.some
      (if tag = 5 then PolicyShape.macroCode p (PolicyShape.siteCode .positiveRepeat) 1 [a,a]
        else some a) := by
    by_cases h : tag = 5
    · simpa only [firstOperand, h, if_true] using
        exactPolicyIndexedShape c p hc (PolicyShape.siteCode .positiveRepeat) 1 [a,a]
    · simp [firstOperand,h]
  have original : PolicyPartial.mergeCoordinate p tag a b =
      (if tag = 5 then PolicyShape.macroCode p (PolicyShape.siteCode .positiveRepeat) 1 [a,a]
        else some a).bind (fun x => PolicyShape.macroCode p
          (PolicyShape.siteCode (if tag = 5 then .activeExp else .activeAdd)) 2 [x,b,1]) := by
    by_cases ht : tag = 5 <;> simp only [PolicyPartial.mergeCoordinate,ht,if_true,if_false,bind]
  rw [original]
  unfold coordinate
  rw [hfirst,Part.bind_some]
  generalize (if tag = 5 then PolicyShape.macroCode p (PolicyShape.siteCode .positiveRepeat) 1 [a,a]
    else some a) = x
  cases x with
  | none => rfl
  | some y =>
    exact exactPolicyIndexedShape c p hc
      (PolicyShape.siteCode (if tag = 5 then .activeExp else .activeAdd)) 2 [y,b,1]

theorem mergeExact : ExactMerge := by
  intro c p hc level tag a b
  let step (acc : Option (List Nat)) (j : Nat) : Option (List Nat) := do
    let xs ← acc
    let x ← PolicyPartial.mergeCoordinate p tag (a.getD j 0) (b.getD j 0)
    pure (xs ++ [x])
  have he (k : Nat) : prefixCode (c,level,tag,a,b) k =
      Part.some ((List.range k).foldl step (some [])) := by
    induction k with
    | zero => rfl
    | succ j ih =>
      change ((prefixCode (c,level,tag,a,b) j).bind (appendCoordinate (c,level,tag,a,b) j)) = _
      rw [ih,Part.bind_some,List.range_succ,List.foldl_append,List.foldl_cons,List.foldl_nil]
      generalize (List.range j).foldl step (some []) = acc
      cases acc with
      | none => rfl
      | some xs =>
        change (coordinate (c,tag,a.getD j 0,b.getD j 0)).map
          (Option.map (fun x => xs ++ [x])) = _
        rw [coordinateExact c p hc,Part.map_some]
        change Part.some ((PolicyPartial.mergeCoordinate p tag (a.getD j 0) (b.getD j 0)).map
          (fun x => xs ++ [x])) = Part.some
            ((PolicyPartial.mergeCoordinate p tag (a.getD j 0) (b.getD j 0)).bind (fun x => some (xs ++ [x])))
        cases PolicyPartial.mergeCoordinate p tag (a.getD j 0) (b.getD j 0) <;> rfl
  exact he (level+2)

private theorem coordinateEquation (q : CoordinateArgs) :
    (firstOperand q).bind (fun o => match o with
      | none => Part.some none
      | some a => PolicyIndexedShape.macroCode
        (q.1,PolicyShape.siteCode (if q.2.1 = 5 then .activeExp else .activeAdd),2,[a,q.2.2.2,1])) =
      coordinate q := rfl

private theorem appendEquation (q : MergeArgs × Nat × Option (List Nat)) :
    (match q.2.2 with
      | none => Part.some none
      | some xs => (coordinate (q.1.1,q.1.2.2.1,
          q.1.2.2.2.1.getD q.2.1 0,q.1.2.2.2.2.getD q.2.1 0)).map
          (Option.map (fun a => xs ++ [a]))) = appendCoordinate q.1 q.2.1 q.2.2 := rfl

private theorem prefixEquation (q : MergeArgs × Nat) :
    q.2.rec (Part.some (some [])) (fun j ih => ih.bind (appendCoordinate q.1 j)) =
      prefixCode q.1 q.2 := rfl

private theorem mergeEquation (q : MergeArgs) : prefixCode q (q.2.1 + 2) = merge q := rfl

attribute [local irreducible] PolicyIndexedShape.macroCode firstOperand coordinate
  appendCoordinate prefixCode merge

theorem coordinatePartrec : Partrec coordinate := by
  have h := onSome remainingPartrec
  apply (operandPartrec.bind h.to₂).of_eq
  intro q
  rw [← coordinateEquation q]
  apply congrArg (fun f : Option Nat → Part (Option Nat) => (firstOperand q).bind f)
  funext o
  cases o <;> rfl

private theorem appendPartrec :
    Partrec (fun q : MergeArgs × Nat × Option (List Nat) => appendCoordinate q.1 q.2.1 q.2.2) := by
  let Q := (MergeArgs × Nat) × List Nat
  have hx : Computable (fun q : Q => q.1.1) := Computable.fst.comp Computable.fst
  have hj : Computable (fun q : Q => q.1.2) := Computable.snd.comp Computable.fst
  have ht : Computable (fun q : Q => q.1.1.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hx))
  have hleft : Computable (fun q : Q => q.1.1.2.2.2.1.getD q.1.2 0) :=
    (Primrec.list_getD 0).to_comp.comp
      (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hx)))) hj
  have hright : Computable (fun q : Q => q.1.1.2.2.2.2.getD q.1.2 0) :=
    (Primrec.list_getD 0).to_comp.comp
      (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp hx)))) hj
  have hcoord : Partrec (fun q : Q =>
      coordinate (q.1.1.1,q.1.1.2.2.1,q.1.1.2.2.2.1.getD q.1.2 0,q.1.1.2.2.2.2.getD q.1.2 0)) :=
    coordinatePartrec.comp ((Computable.fst.comp hx).pair (ht.pair (hleft.pair hright)))
  have hfinish : Computable₂ (fun (q : Q) (o : Option Nat) => o.map (fun a => q.2 ++ [a])) := by
    let R := Q × Option Nat
    have hc : Computable₂ (fun (r : R) (a : Nat) => r.1.2 ++ [a]) :=
      (Primrec.list_concat.to_comp.comp
        (Computable.snd.comp (Computable.fst.comp Computable.fst)) Computable.snd).to₂
    exact (Computable.option_map (Computable.snd : Computable (fun r : R => r.2)) hc).to₂
  have hcase : Partrec₂ (fun (q : MergeArgs × Nat) (xs : List Nat) =>
      (coordinate (q.1.1,q.1.2.2.1,q.1.2.2.2.1.getD q.2 0,q.1.2.2.2.2.getD q.2 0)).map
        (Option.map (fun a => xs ++ [a]))) := (hcoord.map hfinish).to₂
  have adapt : Computable (fun q : MergeArgs × Nat × Option (List Nat) => ((q.1,q.2.1),q.2.2)) :=
    (Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
      (Computable.snd.comp Computable.snd)
  have h := (onSome hcase).comp adapt
  apply h.of_eq
  intro q
  rw [← appendEquation q]
  rcases q with ⟨x,j,o⟩
  cases o <;> rfl

theorem prefixPartrec : Partrec (fun q : MergeArgs × Nat => prefixCode q.1 q.2) := by
  have hs : Partrec₂ (fun (q : MergeArgs × Nat) (arg : Nat × Option (List Nat)) =>
      appendCoordinate q.1 arg.1 arg.2) :=
    (appendPartrec.comp ((Computable.fst.comp Computable.fst).pair Computable.snd)).to₂
  have base : Computable (fun _ : MergeArgs × Nat => (some [] : Option (List Nat))) :=
    Computable.const _
  have h := Partrec.nat_rec Computable.snd base hs
  exact h.of_eq prefixEquation

theorem mergePartrec : Partrec merge := by
  have adapt : Computable (fun q : MergeArgs => (q,q.2.1 + 2)) :=
    Computable.id.pair
      (Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 2))
  exact (prefixPartrec.comp adapt).of_eq mergeEquation

end LogicLineages.StandardControlCurrent.PolicyIndexedMerge
