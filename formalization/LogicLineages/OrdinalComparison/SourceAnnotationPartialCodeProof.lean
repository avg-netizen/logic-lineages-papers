module
public import LogicLineages.OrdinalComparison.SourceAnnotationPartialCodeSemanticProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxPartialComputability
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode.Proof
open SourceAnnotationCode

theorem primitiveRecursive : Targets.PrimitiveRecursive := by
  let children : (Nat×Nat) → List (Nat×Nat) := fun s =>
    if s.2%4=2 then [(s.1,(s.2/4).unpair.1),(s.1,(s.2/4).unpair.2)]
    else if s.2%4=3 then [(s.1,(s.2/4).unpair.2)] else []
  let addAsm : Option Nat → Option Nat → Option Nat := fun a b => do
    let x ← a
    let y ← b
    pure (4*Nat.pair (4*Nat.pair x y+2) 4+2)
  let collapseAsm : Nat → Option Nat → Option Nat := fun op tail =>
    tail.map (fun t => 4*Nat.pair (closeOperatorCode op) t+3)
  let base : (Nat×Nat) → Option Nat := fun s =>
    if OrdinalSyntax.headFree (eraseCode s.1 s.2) then some (4*Nat.pair (closeCode s.2) 4+2)
    else if s.2%4=0 then (OrdinalSyntax.partialRun 0 0 (s.2/4)).map (fun v => 4*v.getD 0 0)
    else none
  let assemble : (Nat×Nat) → List (Option Nat) → Option (Option Nat) := fun s rs => some
    (if OrdinalSyntax.headFree (eraseCode s.1 s.2) then base s
    else if s.2%4=2 then addAsm (rs.getD 0 none) (rs.getD 1 none)
    else if s.2%4=3 then collapseAsm (s.2/4).unpair.1 (rs.getD 0 none) else base s)
  have hn (k : Nat) : Primrec (fun p : Nat×Nat => 4*Nat.pair p.1 p.2+k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 4) Primrec₂.natPair) (Primrec.const k)
  have hpair : Primrec (fun p : Nat×Nat => 4*Nat.pair (4*Nat.pair p.1 p.2+2) 4+2) :=
    (hn 2).comp ((hn 2).pair (Primrec.const 4))
  have happ : Primrec₂ addAsm := by
    have hh : Primrec (fun p : Option Nat × Option Nat =>
        p.1.bind (fun x => p.2.map (fun y => 4*Nat.pair (4*Nat.pair x y+2) 4+2))) :=
      Primrec.option_bind Primrec.fst
        (Primrec.option_map (Primrec.snd.comp Primrec.fst)
          (hpair.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂
    exact hh.of_eq (fun p => by cases p.1 <;> cases p.2 <;> rfl)
  have hclose := SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.2.2.1
  have hlam : Primrec₂ collapseAsm := Primrec.option_map Primrec.snd
    ((hn 3).comp ((hclose.comp (Primrec.fst.comp Primrec.fst)).pair Primrec.snd)).to₂
  have htag : Primrec (fun s : Nat×Nat => s.2%4) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hpay : Primrec (fun s : Nat×Nat => s.2/4) := Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : Nat×Nat => s.2%4=k) := Primrec.eq.comp htag (Primrec.const k)
  have hfree : Primrec (fun s : Nat×Nat => OrdinalSyntax.headFree (eraseCode s.1 s.2)) :=
    OrdinalSyntax.ordinalSyntaxHeadOperationsPrimitiveRecursive.1.comp
      SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.1
  have hf : PrimrecPred (fun s : Nat×Nat => OrdinalSyntax.headFree (eraseCode s.1 s.2)=true) :=
    Primrec.eq.comp hfree (Primrec.const true)
  have hc : Primrec children := Primrec.ite (ht 2)
    (Primrec.list_cons.comp (Primrec.fst.pair hl) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 3) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])) (Primrec.const []))
  have hp : Primrec (fun s : Nat×Nat => OrdinalSyntax.partialRun 0 0 (s.2/4)) :=
    OrdinalSyntax.ordinalSyntaxPartialPrimitiveRecursive.comp ((Primrec.const 0).pair ((Primrec.const 0).pair hpay))
  have hvalue : Primrec (fun s : (Nat×Nat)×List Nat => 4*s.2.getD 0 0) :=
    Primrec.nat_mul.comp (Primrec.const 4) ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0))
  have hb : Primrec base := Primrec.ite hf
    (Primrec.option_some.comp ((hn 2).comp
      ((SourceAnnotationCode.Proof.primitiveRecursiveAlgorithms.2.2.2.comp Primrec.snd).pair (Primrec.const 4))))
    (Primrec.ite (ht 0) (Primrec.option_map hp hvalue.to₂) (Primrec.const none))
  have hasm : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat×Nat)×List (Option Nat) => p.2.getD k none) :=
      (Primrec.list_getD (none : Option Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite (hf.comp Primrec.fst) (hb.comp Primrec.fst)
      (Primrec.ite ((ht 2).comp Primrec.fst) (happ.comp (hg 0) (hg 1))
      (Primrec.ite ((ht 3).comp Primrec.fst) (hlam.comp (hl.comp Primrec.fst) (hg 0)) (hb.comp Primrec.fst))))
  apply Primrec.nat_omega_rec' (fun s : Nat×Nat => groundPartialCode s.1 s.2) Primrec.snd hc hasm
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
    conv_rhs => rw [groundPartialCode]
    by_cases hf : OrdinalSyntax.headFree (eraseCode s.1 s.2)=true
    · simp [assemble,base,hf]
    · have ht : s.2%4=0 ∨ s.2%4=1 ∨ s.2%4=2 ∨ s.2%4=3 := by omega
      rcases ht with h|h|h|h <;> simp [children,assemble,base,h,hf,addAsm,collapseAsm]
end LogicLineages.OrdinalComparison.Source.SourceAnnotationPartialCode.Proof
