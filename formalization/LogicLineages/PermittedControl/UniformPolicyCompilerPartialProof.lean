module
public import LogicLineages.PermittedControl.UniformPolicyCompilerPartialTargets
public import LogicLineages.PermittedControl.UniformPolicyCompilerFixProof
import LogicLineages.PermittedControl.PolicySuppliedCodeMacroProof
import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.UniformPolicyCompiler
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax
open PolicySuppliedCodeMacro (RealizesPolicy macroEval macroPartrec exactMacroCalibration)
open StandardControlCurrent

abbrev Code := Nat.Partrec.Code

/-! ## The supplied macro -/

noncomputable def macroP (e : Code) (tag n : Nat) (xs : List Nat) : Part (Option Nat) :=
  macroEval (e,tag,n,xs)

theorem macroPartrecP : Partrec (fun x : Code × Nat × Nat × List Nat => macroP x.1 x.2.1 x.2.2.1 x.2.2.2) :=
  macroPartrec

theorem macroCal {e : Code} {p : Policy} (he : RealizesPolicy e p) (tag n : Nat) (xs : List Nat) :
    macroP e tag n xs = Part.some (PolicyShape.macroCode p tag n xs) :=
  exactMacroCalibration e p he tag n xs

/-- Composition helper: the macro at computable arguments. -/
theorem macroAt {α : Type} [Primcodable α] {e : α → Code} {tag n : α → Nat} {xs : α → List Nat}
    (he : Computable e) (ht : Computable tag) (hn : Computable n) (hx : Computable xs) :
    Partrec (fun a => macroP (e a) (tag a) (n a) (xs a)) := by
  have h := macroPartrecP.comp (he.pair (ht.pair (hn.pair hx)))
  exact h

/-! ## One merge coordinate -/

noncomputable def coordP (e : Code) (tag a b : Nat) : Part (Option Nat) :=
  pbind (if tag = 5 then macroP e (PolicyShape.siteCode .positiveRepeat) 1 [a,a] else Part.some (some a))
    (fun x => macroP e (PolicyShape.siteCode (if tag = 5 then .activeExp else .activeAdd)) 2 [x,b,1])

theorem coordPartrec : Partrec (fun x : Code × Nat × Nat × Nat => coordP x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let A := Code × Nat × Nat × Nat
  have he : Computable (fun x : A => x.1) := Computable.fst
  have ht : Computable (fun x : A => x.2.1) := Computable.fst.comp Computable.snd
  have ha : Computable (fun x : A => x.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hb : Computable (fun x : A => x.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hP : Computable (fun x : A => decide (x.2.1 = 5)) :=
    (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 5)).decide.to_comp
  have hfirstT : Partrec (fun x : A => macroP x.1 (PolicyShape.siteCode .positiveRepeat) 1 [x.2.2.1,x.2.2.1]) :=
    macroAt he (Computable.const (PolicyShape.siteCode .positiveRepeat)) (Computable.const 1)
      (Primrec.list_cons.to_comp.comp ha (Primrec.list_cons.to_comp.comp ha (Computable.const [])))
  have hfirstF : Partrec (fun x : A => (Part.some (some x.2.2.1) : Part (Option Nat))) :=
    (Computable.option_some.comp ha).partrec
  have hfirst := pite (P := fun x : A => x.2.1 = 5) hP hfirstT hfirstF
  let B := A × Nat
  have hsite : Computable (fun y : B => PolicyShape.siteCode (if y.1.2.1 = 5 then .activeExp else .activeAdd)) := by
    have htag : Primrec (fun y : B => y.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
    have hc : PrimrecPred (fun y : B => y.1.2.1 = 5) := Primrec.eq.comp htag (Primrec.const 5)
    have h := Primrec.ite hc (Primrec.const (PolicyShape.siteCode .activeExp))
      (Primrec.const (PolicyShape.siteCode .activeAdd))
    exact (h.of_eq (fun y => by split <;> rfl)).to_comp
  have hlist : Computable (fun y : B => [y.2,y.1.2.2.2,1]) :=
    Primrec.list_cons.to_comp.comp Computable.snd
      (Primrec.list_cons.to_comp.comp (hb.comp Computable.fst) (Computable.const [1]))
  have hsecond : Partrec (fun y : B =>
      macroP y.1.1 (PolicyShape.siteCode (if y.1.2.1 = 5 then .activeExp else .activeAdd)) 2 [y.2,y.1.2.2.2,1]) :=
    macroAt (he.comp Computable.fst) hsite (Computable.const 2) hlist
  have h := pbindPartrec hfirst hsecond.to₂
  exact h

theorem coordCal {e : Code} {p : Policy} (he : RealizesPolicy e p) (tag a b : Nat) :
    coordP e tag a b = Part.some (PolicyPartial.mergeCoordinate p tag a b) := by
  unfold coordP PolicyPartial.mergeCoordinate
  by_cases h : tag = 5
  · rw [if_pos h,macroCal he]
    simp only [if_pos h]
    exact pbind_calibrated _ _ _ (fun x => macroCal he _ _ _)
  · rw [if_neg h]
    simp only [if_neg h]
    exact pbind_calibrated _ _ _ (fun x => macroCal he _ _ _)

/-! ## The merge -/

noncomputable def mergeStep (e : Code) (tag : Nat) (a b : List Nat) (j : Nat) (acc : Option (List Nat)) :
    Part (Option (List Nat)) :=
  pbind (Part.some acc) (fun xs => pbind (coordP e tag (a.getD j 0) (b.getD j 0)) (fun x => Part.some (some (xs ++ [x]))))

noncomputable def mergeP (e : Code) (level tag : Nat) (a b : List Nat) : Part (Option (List Nat)) :=
  Nat.rec (motive := fun _ => Part (Option (List Nat))) (Part.some (some []))
    (fun j IH => IH.bind (fun acc => mergeStep e tag a b j acc)) (level+2)

theorem mergePartrec : Partrec (fun x : Code × Nat × Nat × List Nat × List Nat =>
    mergeP x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let A := Code × Nat × Nat × List Nat × List Nat
  let B := A × Nat × Option (List Nat)
  have hacc : Partrec (fun y : B => (Part.some y.2.2 : Part (Option (List Nat)))) :=
    (Computable.snd.comp Computable.snd).partrec
  let C := B × List Nat
  have hcoordArgs : Computable (fun z : C => (z.1.1.1,z.1.1.2.2.1,z.1.1.2.2.2.1.getD z.1.2.1 0,
      z.1.1.2.2.2.2.getD z.1.2.1 0)) := by
    have hA : Computable (fun z : C => z.1.1) := Computable.fst.comp Computable.fst
    have hj : Computable (fun z : C => z.1.2.1) := Computable.fst.comp (Computable.snd.comp Computable.fst)
    exact (Computable.fst.comp hA).pair ((Computable.fst.comp (Computable.snd.comp (Computable.snd.comp hA))).pair
      (((Primrec.list_getD 0).to_comp.comp (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp hA)))) hj).pair
      ((Primrec.list_getD 0).to_comp.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp
        (Computable.snd.comp hA)))) hj)))
  have hcoord : Partrec (fun z : C => coordP z.1.1.1 z.1.1.2.2.1 (z.1.1.2.2.2.1.getD z.1.2.1 0)
      (z.1.1.2.2.2.2.getD z.1.2.1 0)) := by
    have h := coordPartrec.comp hcoordArgs
    exact h
  have happ : Partrec₂ (fun (z : C) (x : Nat) => (Part.some (some (z.2 ++ [x])) : Part (Option (List Nat)))) := by
    have h : Computable (fun w : C × Nat => some (w.1.2 ++ [w.2])) :=
      Computable.option_some.comp (Primrec.list_concat.to_comp.comp (Computable.snd.comp Computable.fst) Computable.snd)
    exact h.partrec.to₂
  have hinner : Partrec₂ (fun (y : B) (xs : List Nat) => pbind (coordP y.1.1 y.1.2.2.1 (y.1.2.2.2.1.getD y.2.1 0)
      (y.1.2.2.2.2.getD y.2.1 0)) (fun x => Part.some (some (xs ++ [x])))) :=
    (pbindPartrec hcoord happ).to₂
  have hstep : Partrec₂ (fun (a : A) (q : Nat × Option (List Nat)) =>
      mergeStep a.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2 q.1 q.2) := by
    have h := pbindPartrec hacc hinner
    exact h.to₂
  have hlen : Computable (fun a : A => a.2.1 + 2) :=
    Primrec.nat_add.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const 2)
  have h := Partrec.nat_rec hlen (Computable.const (some ([] : List Nat))).partrec hstep
  exact h

private theorem foldl_range_succ {β : Type} (f : β → Nat → β) (init : β) (k : Nat) :
    (List.range (k+1)).foldl f init = f ((List.range k).foldl f init) k := by
  rw [List.range_succ,List.foldl_append]
  rfl

theorem mergeCal {e : Code} {p : Policy} (he : RealizesPolicy e p) (level tag : Nat) (a b : List Nat) :
    mergeP e level tag a b = Part.some (PolicyPartial.mergeCode p level tag a b) := by
  unfold mergeP PolicyPartial.mergeCode
  generalize level + 2 = k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [foldl_range_succ]
    change (Nat.rec (motive := fun _ => Part (Option (List Nat))) (Part.some (some []))
      (fun j IH => IH.bind (fun acc => mergeStep e tag a b j acc)) k).bind
        (fun acc => mergeStep e tag a b k acc) = _
    rw [ih,Part.bind_some]
    unfold mergeStep
    apply pbind_calibrated
    intro xs
    rw [coordCal he]
    exact pbind_calibrated _ _ _ (fun x => rfl)

/-! ## The partial recursion through the fixed-point theorem -/

abbrev RunArgs := Code × Nat × Nat × Nat

/-- One step of `PolicyPartial.run`, with recursive calls through `G` and the
supplied macro through `macroEval`. -/
noncomputable def runStep (G : RunArgs →. Option (List Nat)) (x : RunArgs) : Part (Option (List Nat)) :=
  if headFree x.2.2.2 = true then Part.some (some (partialFree x.2.1 x.2.2.1 x.2.2.2))
  else if x.2.2.2 % 8 = 3 then
    Part.some (if x.2.2.1 = (x.2.2.2/8).unpair.2 then some (List.replicate (x.2.1+2) 1) else none)
  else if x.2.2.2 % 8 = 4 then
    pbind (G (x.1,x.2.1,x.2.2.1,(x.2.2.2/8).unpair.1)) (fun a =>
      pbind (G (x.1,x.2.1,x.2.2.1,(x.2.2.2/8).unpair.2)) (fun b => mergeP x.1 x.2.1 4 a b))
  else if x.2.2.2 % 8 = 5 then
    (if 0 < x.2.2.1 then
      pbind (G (x.1,x.2.1,x.2.2.1+1,(x.2.2.2/8).unpair.1)) (fun a =>
        pbind (G (x.1,x.2.1,x.2.2.1,(x.2.2.2/8).unpair.2)) (fun b => mergeP x.1 x.2.1 5 a b))
    else Part.some none)
  else if x.2.2.2 % 8 = 6 then
    (if x.2.2.1 = 0 then
      pbind (G (x.1,x.2.1,1,(x.2.2.2/8).unpair.1)) (fun a =>
        pbind (G (x.1,x.2.1,0,(x.2.2.2/8).unpair.2)) (fun b =>
          Part.some (some (partialCollapse x.2.1 (x.2.2.2/8).unpair.1 a b))))
    else Part.some none)
  else Part.some none

private theorem nodePrim {α : Type*} [Primcodable α] {t a b : α → Nat}
    (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node (t x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp ha hb)) ht

private theorem freePrim {α : Type*} [Primcodable α] {l i n : α → Nat}
    (hl : Primrec l) (hi : Primrec i) (hn : Primrec n) :
    Primrec (fun x => partialFree (l x) (i x) (n x)) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hl (Primrec.const 2)))
  exact Primrec.ite (Primrec.eq.comp (hi.comp Primrec.fst) Primrec.snd)
    (nodePrim (Primrec.const 4)
      (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp (hn.comp Primrec.fst))
      (Primrec.const 1)) (Primrec.const 1)

private theorem collapsePrim {α : Type*} [Primcodable α] {l h : α → Nat} {a b : α → List Nat}
    (hl : Primrec l) (hh : Primrec h) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => partialCollapse (l x) (h x) (a x) (b x)) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hl (Primrec.const 2)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (nodePrim (Primrec.const 6)
      (ordinalSyntaxHeadOperationsPrimitiveRecursive.2.1.comp (hh.comp Primrec.fst))
      ((Primrec.list_getD 0).comp (hb.comp Primrec.fst) (Primrec.const 0)))
    (nodePrim (Primrec.const 4)
      ((Primrec.list_getD 0).comp (ha.comp Primrec.fst) Primrec.snd)
      ((Primrec.list_getD 0).comp (hb.comp Primrec.fst) Primrec.snd))

/-- A two-child branch: both recursive calls then a partial continuation. -/
private theorem twoChildren {A : Type} [Primcodable A]
    {c : A → Code} {u v : A → RunArgs} {k : A → List Nat → List Nat →. Option (List Nat)}
    (hc : Computable c) (hu : Computable u) (hv : Computable v)
    (hk : Partrec (fun w : (A × List Nat) × List Nat => k w.1.1 w.1.2 w.2)) :
    Partrec (fun y : A => pbind (decodeEval (c y) (u y) : Part (Option (List Nat)))
      (fun a => pbind (decodeEval (c y) (v y) : Part (Option (List Nat))) (fun b => k y a b))) := by
  have h1 : Partrec (fun y : A => (decodeEval (c y) (u y) : Part (Option (List Nat)))) :=
    decodeEvalPartrec.comp (hc.pair hu)
  have h2 : Partrec (fun w : A × List Nat => (decodeEval (c w.1) (v w.1) : Part (Option (List Nat)))) :=
    decodeEvalPartrec.comp ((hc.comp Computable.fst).pair (hv.comp Computable.fst))
  have hin : Partrec₂ (fun (w : A × List Nat) (b : List Nat) => k w.1 w.2 b) := hk.to₂
  have h3 := pbindPartrec h2 hin
  exact pbindPartrec h1 h3.to₂

theorem runStepPartrec :
    Partrec (fun y : Code × RunArgs => runStep (decodeEval y.1) y.2) := by
  let Y := Code × RunArgs
  have hc : Computable (fun y : Y => y.1) := Computable.fst
  have he : Computable (fun y : Y => y.2.1) := Computable.fst.comp Computable.snd
  have hl : Primrec (fun y : Y => y.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun y : Y => y.2.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hn : Primrec (fun y : Y => y.2.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hd : Primrec (fun y : Y => (y.2.2.2.2/8).unpair) := Primrec.unpair.comp (Primrec.nat_div.comp hn (Primrec.const 8))
  have hq1 : Primrec (fun y : Y => (y.2.2.2.2/8).unpair.1) := Primrec.fst.comp hd
  have hq2 : Primrec (fun y : Y => (y.2.2.2.2/8).unpair.2) := Primrec.snd.comp hd
  have hmod (k : Nat) : Computable (fun y : Y => decide (y.2.2.2.2 % 8 = k)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp hn (Primrec.const 8)) (Primrec.const k)).decide.to_comp
  have hfree : Partrec (fun y : Y => (Part.some (some (partialFree y.2.2.1 y.2.2.2.1 y.2.2.2.2)) :
      Part (Option (List Nat)))) :=
    (Computable.option_some.comp (freePrim hl hi hn).to_comp).partrec
  have hrep : Primrec (fun y : Y => List.replicate (y.2.2.1+2) 1) := by
    have h := Primrec.list_map (Primrec.list_range.comp (Primrec.nat_add.comp hl (Primrec.const 2)))
      (Primrec.const 1).to₂
    exact h.of_eq (fun y => by simp)
  have hthree : Partrec (fun y : Y => (Part.some (if y.2.2.2.1 = (y.2.2.2.2/8).unpair.2 then
      some (List.replicate (y.2.2.1+2) 1) else none) : Part (Option (List Nat)))) :=
    (Primrec.ite (Primrec.eq.comp hi hq2) (Primrec.option_some.comp hrep) (Primrec.const none)).to_comp.partrec
  have hnone : Partrec (fun _ : Y => (Part.some none : Part (Option (List Nat)))) :=
    (Computable.const (none : Option (List Nat))).partrec
  have hmerge (tag : Nat) : Partrec (fun w : (Y × List Nat) × List Nat => mergeP w.1.1.2.1 w.1.1.2.2.1 tag w.1.2 w.2) := by
    have h := mergePartrec.comp ((he.comp (Computable.fst.comp Computable.fst)).pair
      ((hl.to_comp.comp (Computable.fst.comp Computable.fst)).pair ((Computable.const tag).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))))
    exact h
  have hfour := twoChildren (c := fun y : Y => y.1)
    (u := fun y : Y => (y.2.1,y.2.2.1,y.2.2.2.1,(y.2.2.2.2/8).unpair.1))
    (v := fun y : Y => (y.2.1,y.2.2.1,y.2.2.2.1,(y.2.2.2.2/8).unpair.2))
    (k := fun y a b => mergeP y.2.1 y.2.2.1 4 a b) hc
    (he.pair (hl.to_comp.pair (hi.to_comp.pair hq1.to_comp)))
    (he.pair (hl.to_comp.pair (hi.to_comp.pair hq2.to_comp))) (hmerge 4)
  have hfive := twoChildren (c := fun y : Y => y.1)
    (u := fun y : Y => (y.2.1,y.2.2.1,y.2.2.2.1+1,(y.2.2.2.2/8).unpair.1))
    (v := fun y : Y => (y.2.1,y.2.2.1,y.2.2.2.1,(y.2.2.2.2/8).unpair.2))
    (k := fun y a b => mergeP y.2.1 y.2.2.1 5 a b) hc
    (he.pair (hl.to_comp.pair ((Primrec.succ.comp hi).to_comp.pair hq1.to_comp)))
    (he.pair (hl.to_comp.pair (hi.to_comp.pair hq2.to_comp))) (hmerge 5)
  have hcoll : Partrec (fun w : (Y × List Nat) × List Nat =>
      (Part.some (some (partialCollapse w.1.1.2.2.1 (w.1.1.2.2.2.2/8).unpair.1 w.1.2 w.2)) :
        Part (Option (List Nat)))) := by
    have h := collapsePrim (α := (Y × List Nat) × List Nat)
      (hl.comp (Primrec.fst.comp Primrec.fst)) (hq1.comp (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst) Primrec.snd
    exact (Computable.option_some.comp h.to_comp).partrec
  have hsix := twoChildren (c := fun y : Y => y.1)
    (u := fun y : Y => (y.2.1,y.2.2.1,1,(y.2.2.2.2/8).unpair.1))
    (v := fun y : Y => (y.2.1,y.2.2.1,0,(y.2.2.2.2/8).unpair.2))
    (k := fun y a b => Part.some (some (partialCollapse y.2.2.1 (y.2.2.2.2/8).unpair.1 a b))) hc
    (he.pair (hl.to_comp.pair ((Computable.const 1).pair hq1.to_comp)))
    (he.pair (hl.to_comp.pair ((Computable.const 0).pair hq2.to_comp))) hcoll
  have hpos : Computable (fun y : Y => decide (0 < y.2.2.2.1)) :=
    (Primrec.nat_lt.comp (Primrec.const 0) hi).decide.to_comp
  have hzero : Computable (fun y : Y => decide (y.2.2.2.1 = 0)) :=
    (Primrec.eq.comp hi (Primrec.const 0)).decide.to_comp
  have hhead : Computable (fun y : Y => decide (headFree y.2.2.2.2 = true)) :=
    (Primrec.eq.comp (ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp hn) (Primrec.const true)).decide.to_comp
  have h := pite hhead hfree (pite (hmod 3) hthree (pite (hmod 4) hfour
    (pite (hmod 5) (pite hpos hfive hnone) (pite (hmod 6) (pite hzero hsix hnone) hnone))))
  exact h.of_eq (fun y => rfl)

theorem exactUniformPartial : ExactUniformPartial := by
  obtain ⟨G,hG,hfix⟩ := exists_fix runStep runStepPartrec
  refine ⟨G,hG,?_⟩
  intro e p he level i n
  induction n using Nat.strong_induction_on generalizing level i with
  | _ n ih =>
    rw [hfix,PolicyPartial.run]
    unfold runStep
    by_cases hf : headFree n = true
    · simp [hf]
    · by_cases h3 : n % 8 = 3
      · simp [hf,h3]
      · have hpos : n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 → 0 < n := by omega
        have hl : n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 → (n/8).unpair.1 < n := fun h =>
          (Nat.unpair_left_le _).trans_lt (Nat.div_lt_self (hpos h) (by decide))
        have hr : n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 → (n/8).unpair.2 < n := fun h =>
          (Nat.unpair_right_le _).trans_lt (Nat.div_lt_self (hpos h) (by decide))
        rw [if_neg hf,if_neg h3,if_neg hf,if_neg h3]
        by_cases h4 : n % 8 = 4
        · have hb : n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 := Or.inl h4
          rw [if_pos h4,dif_pos hb,if_pos h4,ih _ (hl hb)]
          apply pbind_calibrated
          intro a
          rw [ih _ (hr hb)]
          exact pbind_calibrated _ _ _ (fun b => mergeCal he _ _ _ _)
        · rw [if_neg h4]
          by_cases h5 : n % 8 = 5
          · have hb : n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 := Or.inr (Or.inl h5)
            rw [if_pos h5,dif_pos hb,if_neg h4,if_pos h5]
            by_cases hi : 0 < i
            · rw [if_pos hi,if_pos hi,ih _ (hl hb)]
              apply pbind_calibrated
              intro a
              rw [ih _ (hr hb)]
              exact pbind_calibrated _ _ _ (fun b => mergeCal he _ _ _ _)
            · rw [if_neg hi,if_neg hi]
          · rw [if_neg h5]
            by_cases h6 : n % 8 = 6
            · have hb : n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6 := Or.inr (Or.inr h6)
              rw [if_pos h6,dif_pos hb,if_neg h4,if_neg h5]
              by_cases hi : i = 0
              · rw [if_pos hi,if_pos hi,ih _ (hl hb)]
                apply pbind_calibrated
                intro a
                rw [ih _ (hr hb)]
                exact pbind_calibrated _ _ _ (fun b => rfl)
              · rw [if_neg hi,if_neg hi]
            · have hb : ¬ (n % 8 = 4 ∨ n % 8 = 5 ∨ n % 8 = 6) := by omega
              rw [if_neg h6,dif_neg hb]

#print axioms exactUniformPartial
end LogicLineages.PermittedControl.UniformPolicyCompiler
