module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationMarkerProgramsProof
public import LogicLineages.StandardControlCurrent.PolicyPartialRunPrograms
public import LogicLineages.StandardControlCurrent.ComputableRankedProof
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxHeadProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationPrograms

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum SourceAnnotationCode

theorem partial (p : Policy) (hp : PolicyShape.Effective p) :
    Computable (fun s : Nat × Nat => CurrentGroundAnnotationCode.groundPartialCode p s.1 s.2) := by
  let S := Nat × Nat
  let A := S × List (Option Nat)
  let children : S → List S := fun s =>
    if s.2%4=2 then [(s.1,(s.2/4).unpair.1),(s.1,(s.2/4).unpair.2)]
    else if s.2%4=3 then [(s.1,(s.2/4).unpair.2)] else []
  let addAsm : Option Nat → Option Nat → Option Nat := fun a b => do
    let x ← a
    let y ← b
    CurrentGroundAnnotationCode.macroCode p (PolicyShape.siteCode .activeAdd) 2 [x,y,4]
  let collapseAsm : Nat → Option Nat → Option Nat := fun op tail =>
    tail.map (fun t => 4*Nat.pair (closeOperatorCode op) t+3)
  let base : S → Option Nat := fun s =>
    if OrdinalSyntax.headFree (eraseCode s.1 s.2) then some (4*Nat.pair (closeCode s.2) 4+2)
    else if s.2%4=0 then (PolicyPartial.run p 0 0 (s.2/4)).map (fun v => 4*v.getD 0 0)
    else none
  let assemble : S → List (Option Nat) → Option (Option Nat) := fun s rs => some
    (if OrdinalSyntax.headFree (eraseCode s.1 s.2) then base s
    else if s.2%4=2 then addAsm (rs.getD 0 none) (rs.getD 1 none)
    else if s.2%4=3 then collapseAsm (s.2/4).unpair.1 (rs.getD 0 none) else base s)
  have hadd : Computable (fun x : Option Nat × Option Nat => addAsm x.1 x.2) := by
    have hl : Primrec (fun q : (Option Nat × Option Nat) × Nat × Nat => [q.2.1,q.2.2,4]) :=
      Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.snd.comp Primrec.snd) (Primrec.const [4]))
    exact PolicyPartialMergePrograms.bindTwo Computable.fst Computable.snd
      ((macro p hp).comp ((Computable.const (PolicyShape.siteCode .activeAdd)).pair
        ((Computable.const 2).pair hl.to_comp)))
  have hclose := SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.2.2.1
  have hlam : Primrec₂ collapseAsm := Primrec.option_map Primrec.snd
    ((markerNode 3).comp ((hclose.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂
  have htag : Primrec (fun s : S => s.2%4) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hpay : Primrec (fun s : S => s.2/4) := Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : S => s.2%4=k) := Primrec.eq.comp htag (Primrec.const k)
  have hfree : Primrec (fun s : S => OrdinalSyntax.headFree (eraseCode s.1 s.2)) :=
    OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp
      SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.1
  have hf : PrimrecPred (fun s : S => OrdinalSyntax.headFree (eraseCode s.1 s.2)=true) :=
    Primrec.eq.comp hfree (Primrec.const true)
  have hc : Primrec children := Primrec.ite (ht 2)
    (Primrec.list_cons.comp (Primrec.fst.pair hl) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 3) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])) (Primrec.const []))
  have hp0 : Computable (fun s : S => PolicyPartial.run p 0 0 (s.2/4)) :=
    (PolicyPartialRunPrograms.run p hp).comp ((Computable.const 0).pair ((Computable.const 0).pair hpay.to_comp))
  have hvalue : Primrec (fun s : S × List Nat => 4*s.2.getD 0 0) :=
    Primrec.nat_mul.comp (Primrec.const 4) ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0))
  have hfreeBody : Primrec (fun s : S => some (4*Nat.pair (closeCode s.2) 4+2)) :=
    Primrec.option_some.comp ((markerNode 2).comp
      ((SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.2.2.2.comp Primrec.snd).pair (Primrec.const 4)))
  have hb : Computable base := chooseProgram hf hfreeBody.to_comp
    (chooseProgram (ht 0) (Computable.option_map hp0 hvalue.to_comp.to₂) (Computable.const none))
  have hasm : Computable (fun z : A => assemble z.1 z.2) := by
    have hg (k : Nat) : Primrec (fun z : A => z.2.getD k none) :=
      (Primrec.list_getD (none : Option Nat)).comp Primrec.snd (Primrec.const k)
    exact Computable.option_some.comp (chooseProgram (hf.comp Primrec.fst) (hb.comp Computable.fst)
      (chooseProgram ((ht 2).comp Primrec.fst) (hadd.comp ((hg 0).pair (hg 1)).to_comp)
      (chooseProgram ((ht 3).comp Primrec.fst)
        (hlam.to_comp.comp ((hl.comp Primrec.fst).pair (hg 0)).to_comp) (hb.comp Computable.fst))))
  apply ComputableRankedProof.ranked S (Option Nat)
    (fun s => CurrentGroundAnnotationCode.groundPartialCode p s.1 s.2) (fun s => s.2) children assemble Primrec.snd hc hasm
  · intro s t hm
    change t.2<s.2
    by_cases h2 : s.2%4=2
    · have hd : s.2/4<s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h2,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h3 : s.2%4=3
      · have hd : s.2/4<s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h2,if_pos h3,List.mem_singleton] at hm
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h2,h3] at hm
  · intro s
    conv_rhs => rw [CurrentGroundAnnotationCode.groundPartialCode]
    by_cases hf : OrdinalSyntax.headFree (eraseCode s.1 s.2)=true
    · simp [assemble,base,hf]
    · have ht : s.2%4=0 ∨ s.2%4=1 ∨ s.2%4=2 ∨ s.2%4=3 := by omega
      rcases ht with h|h|h|h <;> simp [children,assemble,base,h,hf,addAsm,collapseAsm]

end LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationPrograms
