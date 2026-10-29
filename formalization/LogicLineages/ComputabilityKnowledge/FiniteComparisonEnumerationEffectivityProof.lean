module

public import LogicLineages.ComputabilityKnowledge.Comparators.FiniteComparisonEnumerationEffectivity
public import LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationProof

@[expose] public section

/-! External Codex continuation: numerical evaluation and genuine recursive
enumeration of source counterexamples. No computable AST instance is assumed. -/
namespace LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationEffectivityProof

open FiniteComparisonEnumeration

private theorem pr_tokenize : Primrec tokenize := by
  let children : List Nat → List (List Nat) := fun xs =>
    if xs.length = 0 then [] else [xs.drop (if xs.head! = 1 then 2 else 1)]
  let assemble : List Nat → List (Option (List Token)) → Option (Option (List Token)) := fun xs rs =>
    some (if xs.length = 0 then some [] else
      if xs.head! = 0 then rs.head!.map ((0,0) :: ·) else
      if xs.head! = 1 then (if 2 ≤ xs.length then rs.head!.map ((1,xs.getD 1 0) :: ·) else none) else
      if xs.head! = 2 then rs.head!.map ((2,0) :: ·) else
      if xs.head! = 3 then rs.head!.map ((3,0) :: ·) else none)
  have hz : PrimrecPred (fun xs : List Nat => xs.length = 0) := Primrec.eq.comp Primrec.list_length (Primrec.const 0)
  have he (n : Nat) : PrimrecPred (fun xs : List Nat => xs.head! = n) := Primrec.eq.comp Primrec.list_headI (Primrec.const n)
  have hchildren : Primrec children := Primrec.ite hz (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.list_drop.comp (Primrec.ite (he 1) (Primrec.const 2) (Primrec.const 1)) Primrec.id) (Primrec.const []))
  have hm (tag : Nat) (payload : List Nat → Nat) (hp : Primrec payload) :
      Primrec (fun p : List Nat × List (Option (List Token)) => p.2.head!.map ((tag,payload p.1) :: ·)) := by
    apply Primrec.option_map (Primrec.list_headI.comp Primrec.snd)
    exact (Primrec.list_cons.comp ((Primrec.const tag).pair (hp.comp (Primrec.fst.comp Primrec.fst))) Primrec.snd).to₂
  have ha : Primrec₂ assemble := by
    apply Primrec.option_some.comp
    apply Primrec.ite (hz.comp Primrec.fst) (Primrec.const (some []))
    apply Primrec.ite ((he 0).comp Primrec.fst) (hm 0 _ (Primrec.const 0))
    apply Primrec.ite ((he 1).comp Primrec.fst)
    · exact Primrec.ite (Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp Primrec.fst))
        (hm 1 _ ((Primrec.list_getD 0).comp Primrec.id (Primrec.const 1))) (Primrec.const none)
    · exact Primrec.ite ((he 2).comp Primrec.fst) (hm 2 _ (Primrec.const 0))
        (Primrec.ite ((he 3).comp Primrec.fst) (hm 3 _ (Primrec.const 0)) (Primrec.const none))
  apply Primrec.nat_omega_rec' tokenize Primrec.list_length hchildren ha
  · intro xs ys hy
    by_cases hz' : xs.length = 0
    · simp only [children,if_pos hz',List.not_mem_nil] at hy
    · simp only [children,if_neg hz',List.mem_singleton] at hy
      subst ys
      split <;> simp only [List.length_drop] <;> omega
  · intro xs
    cases xs with
    | nil => simp [children,assemble,tokenize]
    | cons tag rest =>
      rcases tag with _ | _ | _ | _ | tag
      · simp [children,assemble,tokenize]
      · cases rest <;> simp [children,assemble,tokenize]
      · simp [children,assemble,tokenize]
      · simp [children,assemble,tokenize]
      · simp [children,assemble,tokenize]

private theorem pr_powTwo : Primrec (fun n : Nat => 2^n) := by
  have h : Primrec (Nat.rec 1 (fun _ r : Nat => r*2)) :=
    Primrec.nat_rec₁ 1 (Primrec.nat_mul.comp Primrec.snd (Primrec.const 2)).to₂
  apply h.of_eq
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [ih,pow_succ]

private theorem pr_numericStep : Primrec (fun p : Nat × List Nat × Token × List Nat =>
    numericStep p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let raw : Nat × List Nat × Token × List Nat → Option (List Nat) := fun p =>
    if p.2.2.1.1 = 0 then some (1::p.2.2.2) else
    if p.2.2.1.1 = 1 then
      if p.2.2.1.2 < p.1 then some ((p.2.1.getD p.2.2.1.2 0 + 1)::p.2.2.2) else none
    else if p.2.2.1.1 = 2 then
      if 2 ≤ p.2.2.2.length then some ((p.2.2.2.getD 0 0+p.2.2.2.getD 1 0)::p.2.2.2.drop 2) else none
    else if p.2.2.1.1 = 3 then
      if 2 ≤ p.2.2.2.length then some ((2^(p.2.2.2.getD 0 0)*p.2.2.2.getD 1 0)::p.2.2.2.drop 2) else none
    else none
  have hs : Primrec (fun p : Nat × List Nat × Token × List Nat => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : Nat × List Nat × Token × List Nat => p.2.2.1.1) := Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have hi : Primrec (fun p : Nat × List Nat × Token × List Nat => p.2.2.1.2) := Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
  have he (n : Nat) := Primrec.eq.comp ht (Primrec.const n)
  have hlen := Primrec.nat_le.comp (Primrec.const 2) (Primrec.list_length.comp hs)
  have hg (i : Nat) := (Primrec.list_getD 0).comp hs (Primrec.const i)
  have hd := Primrec.list_drop.comp (Primrec.const 2) hs
  have hr : Primrec raw :=
    Primrec.ite (he 0) (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.const 1) hs))
      (Primrec.ite (he 1)
        (Primrec.ite (Primrec.nat_lt.comp hi Primrec.fst)
          (Primrec.option_some.comp (Primrec.list_cons.comp
            (Primrec.nat_add.comp ((Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.snd) hi) (Primrec.const 1)) hs)) (Primrec.const none))
        (Primrec.ite (he 2)
          (Primrec.ite hlen (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.nat_add.comp (hg 0) (hg 1)) hd)) (Primrec.const none))
          (Primrec.ite (he 3)
            (Primrec.ite hlen (Primrec.option_some.comp (Primrec.list_cons.comp (Primrec.nat_mul.comp (pr_powTwo.comp (hg 0)) (hg 1)) hd)) (Primrec.const none)) (Primrec.const none))))
  apply hr.of_eq
  rintro ⟨d,values,⟨tag,i⟩,stack⟩
  rcases tag with _ | _ | _ | _ | tag
  · rfl
  · simp [raw,numericStep,tupleValue]
  · cases stack with
    | nil => simp [raw,numericStep]
    | cons a stack => cases stack <;> simp [raw,numericStep]
  · cases stack with
    | nil => simp [raw,numericStep]
    | cons a stack => cases stack <;> simp [raw,numericStep]
  · simp [raw,numericStep]

private theorem pr_numericStack : Primrec (fun p : Nat × List Nat × List Token => numericStack p.1 p.2.1 p.2.2) := by
  unfold numericStack
  apply Primrec.list_foldr (h := fun p q => q.2.bind (numericStep p.1 p.2.1 q.1))
    (Primrec.snd.comp Primrec.snd) (Primrec.const (some []))
  apply Primrec.option_bind (Primrec.snd.comp Primrec.snd)
  refine (pr_numericStep.comp (g := fun p : ((Nat × List Nat × List Token) × Token × Option (List Nat)) × List Nat =>
    (p.1.1.1,p.1.1.2.1,p.1.2.1,p.2)) ?_).to₂
  exact (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)).pair
    ((Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))

private def singletonValue : List Nat → Option Nat
  | [x] => some x
  | _ => none

private theorem pr_singletonValue : Primrec singletonValue := by
  have h : Primrec (fun xs : List Nat => if xs.length = 1 then some xs.head! else none) :=
    Primrec.ite (Primrec.eq.comp Primrec.list_length (Primrec.const 1))
      (Primrec.option_some.comp Primrec.list_headI) (Primrec.const none)
  apply h.of_eq
  intro xs
  cases xs with
  | nil => rfl
  | cons x xs => cases xs <;> simp [singletonValue]

private theorem pr_evalCode : Primrec (fun p : Nat × List Nat × List Nat => evalCode p.1 p.2.1 p.2.2) := by
  have hstack : Primrec (fun p : (Nat × List Nat × List Nat) × List Token => numericStack p.1.1 p.1.2.2 p.2) :=
    pr_numericStack.comp ((Primrec.fst.comp Primrec.fst).pair ((Primrec.snd.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  exact Primrec.option_bind (pr_tokenize.comp (Primrec.fst.comp Primrec.snd))
    (Primrec.option_bind hstack (pr_singletonValue.comp Primrec.snd).to₂).to₂

private theorem pr_evalPair : Primrec (fun p : List Nat × List Nat => evalPair p.1 p.2) := by
  let raw : List Nat × List Nat → Option (Nat × Nat) := fun p =>
    if 3 ≤ p.1.length then
      if (p.1.drop 3).length = p.1.getD 1 0 + p.1.getD 2 0 then
        (evalCode (p.1.getD 0 0) ((p.1.drop 3).take (p.1.getD 1 0)) p.2).bind fun a =>
          (evalCode (p.1.getD 0 0) ((p.1.drop 3).drop (p.1.getD 1 0)) p.2).map (fun b => (a,b))
      else none
    else none
  have hg (i : Nat) := (Primrec.list_getD 0).comp (Primrec.fst : Primrec (fun p : List Nat × List Nat => p.1)) (Primrec.const i)
  have hd := Primrec.list_drop.comp (Primrec.const 3) (Primrec.fst : Primrec (fun p : List Nat × List Nat => p.1))
  have hl : Primrec (fun p : List Nat × List Nat => evalCode (p.1.getD 0 0) ((p.1.drop 3).take (p.1.getD 1 0)) p.2) :=
    pr_evalCode.comp ((hg 0).pair ((Primrec.list_take.comp (hg 1) hd).pair Primrec.snd))
  have hr : Primrec (fun p : List Nat × List Nat => evalCode (p.1.getD 0 0) ((p.1.drop 3).drop (p.1.getD 1 0)) p.2) :=
    pr_evalCode.comp ((hg 0).pair ((Primrec.list_drop.comp (hg 1) hd).pair Primrec.snd))
  have h : Primrec raw := by
    apply Primrec.ite (Primrec.nat_le.comp (Primrec.const 3) (Primrec.list_length.comp Primrec.fst))
    · apply Primrec.ite (Primrec.eq.comp (Primrec.list_length.comp hd) (Primrec.nat_add.comp (hg 1) (hg 2)))
      · exact Primrec.option_bind hl (Primrec.option_map (hr.comp Primrec.fst)
          ((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂).to₂
      · exact Primrec.const none
    · exact Primrec.const none
  apply h.of_eq
  rintro ⟨xs,values⟩
  cases xs with
  | nil => rfl
  | cons d xs => cases xs with
    | nil => rfl
    | cons na xs => cases xs with
      | nil => rfl
      | cons nb rest =>
        have hdrop : (d::na::nb::rest).drop (3+na) = rest.drop na := by
          rw [Nat.add_comm]
          rfl
        simp [raw,evalPair,hdrop,Option.map_eq_bind]

private theorem pr_enumValues : Primrec enumValues :=
  Primrec.option_getD.comp (Primrec.decode (α := List Nat)) (Primrec.const [])

private theorem pr_checkStrict : Primrec (fun p : List Nat × Nat => checkStrict p.1 p.2) := by
  have hs : Primrec₂ (fun _ : List Nat × Nat => fun q : Nat × Nat => decide (¬ q.1 < q.2)) :=
    ((Primrec.nat_lt.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).not.decide).to₂
  have h := Primrec.option_casesOn
    (pr_evalPair.comp (Primrec.fst.pair (pr_enumValues.comp Primrec.snd))) (Primrec.const false) hs
  exact h.of_eq (fun p => by unfold checkStrict; cases evalPair p.1 (enumValues p.2) <;> rfl)

private theorem pr_checkWeak : Primrec (fun p : List Nat × Nat => checkWeak p.1 p.2) := by
  have hs : Primrec₂ (fun _ : List Nat × Nat => fun q : Nat × Nat => decide (¬ q.1 ≤ q.2)) :=
    ((Primrec.nat_le.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).not.decide).to₂
  have h := Primrec.option_casesOn
    (pr_evalPair.comp (Primrec.fst.pair (pr_enumValues.comp Primrec.snd))) (Primrec.const false) hs
  exact h.of_eq (fun p => by unfold checkWeak; cases evalPair p.1 (enumValues p.2) <;> rfl)

private theorem re_of_search (f : List Nat → Nat → Bool) (hf : Computable₂ f)
    (P : List Nat → Prop) (hP : ∀ xs, P xs ↔ ∃ k, f xs k = true) : REPred P := by
  have h : Partrec (fun xs => Nat.rfind (fun k => Part.some (f xs k))) := Partrec.rfind hf.partrec
  apply h.dom_re.of_eq
  intro xs
  simpa only [Nat.rfind_dom,Part.mem_some_iff,Part.some_dom,true_and,and_true,implies_true,forall_const,eq_comm] using (hP xs).symm

theorem finiteComparisonEnumerationEffectivity : Comparators.FiniteComparisonEnumerationEffectivity.Target :=
  ⟨pr_evalCode.to_comp,pr_checkStrict.to_comp,pr_checkWeak.to_comp,
    re_of_search checkStrict pr_checkStrict.to_comp.to₂ StrictCounterexample
      FiniteComparisonEnumerationProof.counterexampleEnumeration.1,
    re_of_search checkWeak pr_checkWeak.to_comp.to₂ WeakCounterexample
      FiniteComparisonEnumerationProof.counterexampleEnumeration.2⟩

end LogicLineages.ComputabilityKnowledge.FiniteComparisonEnumerationEffectivityProof
