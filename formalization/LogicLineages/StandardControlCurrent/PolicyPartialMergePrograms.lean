module
public import LogicLineages.StandardControlCurrent.PolicyPartialTargets
public import LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof
public import LogicLineages.StandardControlCurrent.ComputableFoldProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyPartialMergePrograms
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax

theorem bindTwo {α β γ δ : Type} [Primcodable α] [Primcodable β] [Primcodable γ] [Primcodable δ]
    {a : α → Option β} {b : α → Option γ} {f : α → β → γ → Option δ}
    (ha : Computable a) (hb : Computable b)
    (hf : Computable (fun p : α × β × γ => f p.1 p.2.1 p.2.2)) :
    Computable (fun x => do let u ← a x; let v ← b x; f x u v) := by
  have hinner : Computable (fun p : α × β => (b p.1).bind (f p.1 p.2)) :=
    Computable.option_bind (hb.comp Computable.fst)
      (hf.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.snd.comp Computable.fst).pair Computable.snd))).to₂
  exact Computable.option_bind ha hinner.to₂

attribute [local irreducible] PolicyShape.macroCode

theorem firstOperand (p : Policy) (hp : PolicyShape.Effective p) : Computable (fun x : Nat × Nat × Nat =>
      if x.1=5 then PolicyShape.macroCode p (PolicyShape.siteCode .positiveRepeat) 1 [x.2.1,x.2.1]
      else some x.2.1) := by
    have hm := (PolicyShapeProgramsProof.policies p hp).1
    apply (Computable.cond ((Primrec.beq.comp Primrec.fst (Primrec.const 5)).to_comp)
      (Computable.comp (f := fun q : Nat × Nat × List Nat => PolicyShape.macroCode p q.1 q.2.1 q.2.2)
        (g := fun x : Nat × Nat × Nat => (PolicyShape.siteCode .positiveRepeat,1,[x.2.1,x.2.1])) hm
        ((Computable.const (PolicyShape.siteCode .positiveRepeat)).pair
        ((Computable.const 1).pair
          (Primrec.list_cons.to_comp.comp (Computable.fst.comp Computable.snd)
            (Primrec.list_cons.to_comp.comp (Computable.fst.comp Computable.snd) (Computable.const []))))))
      (Computable.option_some.comp (Computable.fst.comp Computable.snd))).of_eq
    intro x; simp only [Bool.cond_eq_ite,beq_iff_eq]

theorem siteProgram : Primrec (fun x : (Nat × Nat × Nat) × Nat =>
      PolicyShape.siteCode (if x.1.1=5 then .activeExp else .activeAdd)) := by
    exact (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 5))
      (Primrec.const (PolicyShape.siteCode .activeExp))
      (Primrec.const (PolicyShape.siteCode .activeAdd))).of_eq (fun x => by split <;> rfl)

theorem remainingOperands (p : Policy) (hp : PolicyShape.Effective p) : Computable (fun x : (Nat × Nat × Nat) × Nat =>
      PolicyShape.macroCode p (PolicyShape.siteCode (if x.1.1=5 then .activeExp else .activeAdd))
        2 [x.2,x.1.2.2,1]) := by
    have hm := (PolicyShapeProgramsProof.policies p hp).1
    exact Computable.comp (f := fun q : Nat × Nat × List Nat => PolicyShape.macroCode p q.1 q.2.1 q.2.2)
      (g := fun x : (Nat × Nat × Nat) × Nat =>
        (PolicyShape.siteCode (if x.1.1=5 then .activeExp else .activeAdd),2,[x.2,x.1.2.2,1])) hm
      (siteProgram.to_comp.pair ((Computable.const 2).pair
      (Primrec.list_cons.to_comp.comp Computable.snd
        (Primrec.list_cons.to_comp.comp (Computable.snd.comp (Computable.snd.comp Computable.fst))
          (Computable.const [1])))))

theorem coordinate (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × Nat => PolicyPartial.mergeCoordinate p x.1 x.2.1 x.2.2) := by
  unfold PolicyPartial.mergeCoordinate
  exact Computable.option_bind (firstOperand p hp) (remainingOperands p hp).to₂

theorem merge (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun x : Nat × Nat × List Nat × List Nat =>
      PolicyPartial.mergeCode p x.1 x.2.1 x.2.2.1 x.2.2.2) := by
  let A := Nat × Nat × List Nat × List Nat
  have hcoord : Computable (fun x : A × Option (List Nat) × Nat =>
      PolicyPartial.mergeCoordinate p x.1.2.1 (x.1.2.2.1.getD x.2.2 0)
        (x.1.2.2.2.getD x.2.2 0)) :=
    Computable.comp (f := fun q : Nat × Nat × Nat => PolicyPartial.mergeCoordinate p q.1 q.2.1 q.2.2)
      (g := fun x : A × Option (List Nat) × Nat =>
        (x.1.2.1, x.1.2.2.1.getD x.2.2 0, x.1.2.2.2.getD x.2.2 0))
      (coordinate p hp)
      ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
        (((Primrec.list_getD 0).to_comp.comp
          (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          (Computable.snd.comp Computable.snd)).pair
        ((Primrec.list_getD 0).to_comp.comp
          (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp Computable.fst)))
          (Computable.snd.comp Computable.snd))))
  have hstep : Computable (fun x : A × Option (List Nat) × Nat => do
      let xs ← x.2.1
      let v ← PolicyPartial.mergeCoordinate p x.1.2.1 (x.1.2.2.1.getD x.2.2 0)
        (x.1.2.2.2.getD x.2.2 0)
      pure (xs++[v])) :=
    bindTwo (Computable.fst.comp Computable.snd) hcoord
      (Computable.option_some.comp (Primrec.list_concat.to_comp.comp
        (Computable.fst.comp Computable.snd) (Computable.snd.comp Computable.snd)))
  exact ComputableFoldProof.listFold A Nat (Option (List Nat))
    (fun x => List.range (x.1+2)) (fun _ => some [])
    (fun x acc j => do let xs ← acc; let v ← PolicyPartial.mergeCoordinate p x.2.1
      (x.2.2.1.getD j 0) (x.2.2.2.getD j 0); pure (xs++[v]))
    (Primrec.list_range.to_comp.comp
      (Primrec.nat_add.to_comp.comp Computable.fst (Computable.const 2)))
    (Computable.const (some [])) hstep
end LogicLineages.StandardControlCurrent.PolicyPartialMergePrograms
