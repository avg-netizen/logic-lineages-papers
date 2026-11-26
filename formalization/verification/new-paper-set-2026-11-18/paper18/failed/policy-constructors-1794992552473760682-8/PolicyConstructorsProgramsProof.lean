module
public import LogicLineages.StandardControlCurrent.PolicyConstructorsTargets
public import LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxComputability

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyConstructorsProgramsProof
open OrdinalComparison Source Source.AdmissibleSum Source.OrdinalSyntax PolicyConstructors

private theorem nodePrim {α : Type} [Primcodable α] {t a b : α → Nat}
    (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) : Primrec (fun x => node (t x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp ha hb)) ht

private def recFields (input result two : Nat) : List Nat :=
  (List.range (result+1)).map (fun i => if i=0 then two else if i=input+2 then 2 else 1)

private theorem recFieldsPrim : Primrec (fun x : Nat × Nat × Nat => recFields x.1 x.2.1 x.2.2) := by
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp (Primrec.fst.comp Primrec.snd)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.ite (Primrec.eq.comp Primrec.snd
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.fst) (Primrec.const 2)))
      (Primrec.const 2) (Primrec.const 1))

private def appFields (result arg : Nat) (f g : List Nat) (tail : Nat) : List Nat :=
  (List.range (result+1)).map (fun i => if i=0 then node 6 (boxPositive arg f g 1) tail
    else boxPositive arg f g i)

private theorem appFieldsPrim : Primrec (fun x : Nat × Nat × List Nat × List Nat × Nat =>
    appFields x.1 x.2.1 x.2.2.1 x.2.2.2.1 x.2.2.2.2) := by
  let P := Nat × Nat × List Nat × List Nat × Nat
  apply Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
  have ha : Primrec (fun x : P × Nat => x.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hf : Primrec (fun x : P × Nat => x.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hg : Primrec (fun x : P × Nat => x.1.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have ht : Primrec (fun x : P × Nat => x.1.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have bp {i : P × Nat → Nat} (hi : Primrec i) : Primrec (fun x => boxPositive x.1.2.1 x.1.2.2.1 x.1.2.2.2.1 (i x)) :=
    ordinalSyntaxBoxOperationsPrimitiveRecursive.1.comp (ha.pair (hf.pair (hg.pair hi)))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (nodePrim (Primrec.const 6) (bp (Primrec.const 1)) ht) (bp Primrec.snd)

attribute [local irreducible] PolicyShape.macroCode PolicyShape.repeatCode boxPositive recFields appFields

theorem programs : PolicyConstructorsTargets.Programs := by
  constructor
  · apply (Primrec.list_map (Primrec.list_range.comp Primrec.succ) (Primrec.const 1).to₂).of_eq
    intro n
    simp [onesCode]
  · intro p hp
    obtain ⟨hm,hr⟩ := PolicyShapeProgramsProof.policies p hp
    have hrec : Computable (fun x : Nat × Nat => recursorCode p x.1 x.2) := by
      have hnum : Computable (fun _ : Nat × Nat => PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) 2 1) :=
        hr.comp (Computable.const (PolicyShape.siteCode .numeral,2,1))
      have hbody : Computable₂ (fun x : Nat × Nat => fun two : Nat => recFields x.1 x.2 two) :=
        (recFieldsPrim.to_comp.comp ((Computable.fst.comp Computable.fst).pair
          ((Computable.snd.comp Computable.fst).pair Computable.snd))).to₂
      apply (Computable.option_map hnum hbody).of_eq
      intro x
      unfold recursorCode recFields
      cases he : PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) 2 1 <;>
        simp [he,bind,pure]
    have htail : Computable (fun x : Nat × Nat × Nat => boxTailCode p x.1 x.2.1 x.2.2) := by
      let A := Nat × Nat × Nat
      have hnum : Computable (fun x : A => PolicyShape.repeatCode p (PolicyShape.siteCode .numeral) x.1 1) :=
        hr.comp ((Computable.const (PolicyShape.siteCode .numeral)).pair
          (Computable.fst.pair (Computable.const 1)))
      have hlist : Primrec (fun x : A × Nat => [x.1.2.1,x.1.2.2,x.2]) :=
        Primrec.list_cons.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
          (Primrec.list_cons.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
            (Primrec.list_cons.comp Primrec.snd (Primrec.const [])))
      have hbody : Computable₂ (fun x : A => fun n : Nat => PolicyShape.macroCode p
          (PolicyShape.siteCode .optionalBoxTail) 2 [x.2.1,x.2.2,n]) :=
        (hm.comp ((Computable.const (PolicyShape.siteCode .optionalBoxTail)).pair
          ((Computable.const 2).pair hlist.to_comp))).to₂
      have hb := Computable.option_bind hnum hbody
      have hz : Computable (fun x : A => some (node 4 x.2.1 x.2.2)) :=
        Primrec.option_some.to_comp.comp ((nodePrim (Primrec.const 4)
          (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to_comp)
      apply (Computable.cond ((Primrec.beq.comp Primrec.fst (Primrec.const 0)).to_comp) hz hb).of_eq
      intro x
      simp only [boxTailCode,Bool.cond_eq_ite,beq_iff_eq,bind]
    refine ⟨hrec,htail,?_⟩
    let P := Nat × Nat × List Nat × List Nat
    have hf : Primrec (fun x : P => x.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
    have hg : Primrec (fun x : P => x.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
    have ht : Computable (fun x : P => boxTailCode p x.2.1 (x.2.2.1.getD 0 0) (x.2.2.2.getD 0 0)) :=
      Computable.comp (f := fun x : Nat × Nat × Nat => boxTailCode p x.1 x.2.1 x.2.2)
        (g := fun x : P => (x.2.1,x.2.2.1.getD 0 0,x.2.2.2.getD 0 0)) htail
        ((Computable.fst.comp Computable.snd).pair
        (((Primrec.list_getD 0).comp hf (Primrec.const 0)).to_comp.pair
         ((Primrec.list_getD 0).comp hg (Primrec.const 0)).to_comp))
    have hbody : Computable₂ (fun x : P => fun tail : Nat => appFields x.1 x.2.1 x.2.2.1 x.2.2.2 tail) :=
      (appFieldsPrim.to_comp.comp ((Computable.fst.comp Computable.fst).pair
        ((Computable.fst.comp (Computable.snd.comp Computable.fst)).pair
          ((hf.to_comp.comp Computable.fst).pair ((hg.to_comp.comp Computable.fst).pair Computable.snd))))).to₂
    apply (Computable.option_map ht hbody).of_eq
    intro x
    unfold PolicyConstructors.applicationCode appFields
    cases he : boxTailCode p x.2.1 (x.2.2.1.getD 0 0) (x.2.2.2.getD 0 0) <;>
      simp [he,bind,pure]
end LogicLineages.StandardControlCurrent.PolicyConstructorsProgramsProof
