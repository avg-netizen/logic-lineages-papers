module
public import LogicLineages.OrdinalComparison.OriginalBudgetCodeTargets
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  have hm := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hd := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
  have hi := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hz := Primrec.eq.comp hi (Primrec.const 0)
  have hf : Primrec OrdinalSyntax.headLeafFree := Primrec.ite
    (Primrec.eq.comp hm (Primrec.const 3)) hz.not.decide (Primrec.const true)
  have hl : Primrec (fun n : Nat => (OrdinalSyntax.headLeafFree n,1,1)) :=
    hf.pair ((Primrec.const 1).pair (Primrec.const 1))
  have hb : Primrec (fun p : Nat×(Bool×Nat×Nat)×(Bool×Nat×Nat) =>
      (p.2.1.1 && p.2.2.1,
       if p.2.1.1 && p.2.2.1 then 1 else if p.1=4 then p.2.1.2.1+p.2.2.2.1+1 else 1,
       if p.2.1.1 && p.2.2.1 then 1 else if p.1=4 then p.2.1.2.2+p.2.2.2.2+1
         else if p.1=6 then p.2.1.2.1+p.2.2.2.2 else 1)) := by
    let P := Nat×(Bool×Nat×Nat)×(Bool×Nat×Nat)
    have ha : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
    have hb : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
    have hh := Primrec.and.comp (Primrec.fst.comp ha) (Primrec.fst.comp hb)
    have hfree := Primrec.eq.comp hh (Primrec.const true)
    have h4 : PrimrecPred (fun p : P => p.1=4) := Primrec.eq.comp Primrec.fst (Primrec.const 4)
    have h6 : PrimrecPred (fun p : P => p.1=6) := Primrec.eq.comp Primrec.fst (Primrec.const 6)
    have hha := Primrec.fst.comp (Primrec.snd.comp ha)
    have hhb := Primrec.fst.comp (Primrec.snd.comp hb)
    have hsa := Primrec.snd.comp (Primrec.snd.comp ha)
    have hsb := Primrec.snd.comp (Primrec.snd.comp hb)
    exact hh.pair ((Primrec.ite hfree (Primrec.const 1)
      (Primrec.ite h4 (Primrec.nat_add.comp (Primrec.nat_add.comp hha hhb) (Primrec.const 1)) (Primrec.const 1))).pair
      (Primrec.ite hfree (Primrec.const 1)
        (Primrec.ite h4 (Primrec.nat_add.comp (Primrec.nat_add.comp hsa hsb) (Primrec.const 1))
          (Primrec.ite h6 (Primrec.nat_add.comp hha hsb) (Primrec.const 1)))))
  have hc : Primrec countData := OrdinalSyntax.ordinalSyntaxFoldPrimitiveRecursive _ _ _ hl hb
  have hs : Primrec secondCode := Primrec.snd.comp (Primrec.snd.comp hc)
  refine ⟨hc,hs,?_⟩
  exact Primrec.option_map DefaultSourceAssignment.Proof.assignmentPrimitiveRecursive
    (hs.comp ((Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const 0))).to₂
end LogicLineages.OrdinalComparison.Source.OriginalBudgetCode.Proof
