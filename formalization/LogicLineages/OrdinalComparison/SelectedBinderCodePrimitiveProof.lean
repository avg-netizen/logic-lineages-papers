module
public import LogicLineages.OrdinalComparison.SelectedBinderCodeTargets
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SelectedBinderCode.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem index_primitive : Primrec (fun p : Nat×Nat×Nat => indexCode p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat×Nat×Nat => p.1) := Primrec.fst
  have hs : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hj := Primrec.nat_sub.comp hi hd
  exact Primrec.ite (Primrec.nat_lt.comp hi hd) hi
    (Primrec.nat_add.comp hd
      (Primrec.ite (Primrec.nat_lt.comp hj hs) (Primrec.succ.comp hj)
        (Primrec.ite (Primrec.eq.comp hj hs) (Primrec.const 0) hj)))

private theorem source_swapped_primitive : Primrec (fun s : Nat×Nat×Nat => sourceCode s.2.1 s.1 s.2.2) := by
  have hi : Primrec (fun s : Nat×Nat×Nat => s.2.2) := Primrec.snd.comp Primrec.snd
  have hdp : Primrec (fun s : Nat×Nat×Nat => s.2.1) := Primrec.fst.comp Primrec.snd
  have hvar : Primrec (fun s : Nat×Nat×Nat => 8*indexCode s.2.1 s.1 s.2.2) :=
    Primrec.nat_mul.comp (Primrec.const 8)
      (index_primitive.comp (hdp.pair (Primrec.fst.pair hi)))
  let children : (Nat×Nat×Nat) → List (Nat×Nat×Nat) := fun s =>
    if s.2.2%8=5 then [(s.1,s.2.1,(s.2.2/8).unpair.1),(s.1,s.2.1,(s.2.2/8).unpair.2)]
    else if s.2.2%8=6 then [(s.1,s.2.1+1,(s.2.2/8).unpair.2)] else []
  let base : (Nat×Nat×Nat) → Nat := fun s =>
    if s.2.2%8=0 then 8*indexCode s.2.1 s.1 (s.2.2/8)
    else if s.2.2%8=1 then 1
    else if s.2.2%8=2 then if s.2.2/8=0 then 2 else 1
    else if s.2.2%8=3 then s.2.2
    else if s.2.2%8=4 then s.2.2 else 1
  let assemble : (Nat×Nat×Nat) → List Nat → Option Nat := fun s rs => some
    (if s.2.2%8=5 then 8*Nat.pair (rs.getD 0 1) (rs.getD 1 1)+5
    else if s.2.2%8=6 then 8*Nat.pair (s.2.2/8).unpair.1 (rs.getD 0 1)+6
    else base s)
  have hn (k : Nat) : Primrec (fun p : Nat×Nat => 8*Nat.pair p.1 p.2+k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const k)
  have htag : Primrec (fun s : Nat×Nat×Nat => s.2.2%8) :=
    Primrec.nat_mod.comp hi (Primrec.const 8)
  have hpay : Primrec (fun s : Nat×Nat×Nat => s.2.2/8) :=
    Primrec.nat_div.comp hi (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : Nat×Nat×Nat => s.2.2%8=k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hz : PrimrecPred (fun s : Nat×Nat×Nat => s.2.2/8=0) :=
    Primrec.eq.comp hpay (Primrec.const 0)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair (hdp.pair hl))
      (Primrec.list_cons.comp (Primrec.fst.pair (hdp.pair hr)) (Primrec.const [])))
    (Primrec.ite (ht 6)
      (Primrec.list_cons.comp (Primrec.fst.pair ((Primrec.succ.comp hdp).pair hr)) (Primrec.const []))
      (Primrec.const []))
  have hb : Primrec base := Primrec.ite (ht 0)
    (hvar.comp (Primrec.fst.pair (hdp.pair hpay)))
    (Primrec.ite (ht 1) (Primrec.const 1)
    (Primrec.ite (ht 2) (Primrec.ite hz (Primrec.const 2) (Primrec.const 1))
    (Primrec.ite (ht 3) hi
    (Primrec.ite (ht 4) hi (Primrec.const 1)))))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat×Nat×Nat)×List Nat => p.2.getD k 1) :=
      (Primrec.list_getD (1 : Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((ht 5).comp Primrec.fst)
      ((hn 5).comp ((hg 0).pair (hg 1)))
      (Primrec.ite ((ht 6).comp Primrec.fst)
        ((hn 6).comp ((hl.comp Primrec.fst).pair (hg 0))) (hb.comp Primrec.fst)))
  apply Primrec.nat_omega_rec' (fun s : Nat×Nat×Nat => sourceCode s.2.1 s.1 s.2.2) hi hc ha
  · intro s t hmem
    change t.2.2 < s.2.2
    by_cases h5 : s.2.2%8=5
    · have hd : s.2.2/8<s.2.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2.2%8=6
      · have hd : s.2.2/8<s.2.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hmem
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hmem
  · intro s
    conv_rhs => rw [sourceCode]
    have ht : s.2.2%8=0 ∨ s.2.2%8=1 ∨ s.2.2%8=2 ∨ s.2.2%8=3 ∨ s.2.2%8=4 ∨ s.2.2%8=5 ∨ s.2.2%8=6 ∨ s.2.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,base,h]

private theorem ordinal_paired_primitive : Primrec (fun s : (Nat×Nat)×Nat => ordinalCode s.1.1 s.1.2 s.2) := by
  have hm : Primrec (fun s : (Nat×Nat)×Nat => s.2%8) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  have hd : Primrec (fun s : (Nat×Nat)×Nat => s.2/8) := Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hdepth : Primrec (fun s : (Nat×Nat)×Nat => s.1.1) := Primrec.fst.comp Primrec.fst
  have hcount : Primrec (fun s : (Nat×Nat)×Nat => s.1.2) := Primrec.snd.comp Primrec.fst
  have hindex := index_primitive.comp (hdepth.pair (hcount.pair hl))
  have hleaf : Primrec (fun s : (Nat×Nat)×Nat => ordinalLeaf s.1.1 s.1.2 s.2) :=
    Primrec.ite (Primrec.eq.comp hm (Primrec.const 3))
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp hindex hr)) (Primrec.const 3)) Primrec.snd
  let atom : ((Nat×Nat)×Nat) → Prop := fun s => s.2%8<4 ∨ s.2%8=7
  let children : ((Nat×Nat)×Nat) → List ((Nat×Nat)×Nat) := fun s =>
    if atom s then [] else [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
  let assemble : ((Nat×Nat)×Nat) → List Nat → Option Nat := fun s rs => some
    (if atom s then ordinalLeaf s.1.1 s.1.2 s.2
     else 8*Nat.pair (rs.getD 0 0) (rs.getD 1 0)+s.2%8)
  have hatom : PrimrecPred atom :=
    (Primrec.nat_lt.comp hm (Primrec.const 4)).or (Primrec.eq.comp hm (Primrec.const 7))
  have hc : Primrec children := Primrec.ite hatom (Primrec.const [])
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : ((Nat×Nat)×Nat)×List Nat => p.2.getD k 0) :=
      (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite (hatom.comp Primrec.fst)
      (hleaf.comp Primrec.fst)
      (Primrec.nat_add.comp
        (Primrec.nat_mul.comp (Primrec.const 8) (Primrec₂.natPair.comp (hg 0) (hg 1)))
        (hm.comp Primrec.fst)))
  apply Primrec.nat_omega_rec' (fun s : (Nat×Nat)×Nat => ordinalCode s.1.1 s.1.2 s.2) Primrec.snd hc ha
  · intro s t ht
    by_cases h : atom s
    · simp [children,h] at ht
    have hn : 0<s.2 := by simp only [atom] at h;omega
    have hdiv := Nat.div_lt_self hn (show 1<8 by decide)
    simp only [children,if_neg h,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl
    · exact (Nat.unpair_left_le _).trans_lt hdiv
    · exact (Nat.unpair_right_le _).trans_lt hdiv
  · intro s
    conv_rhs => rw [ordinalCode,OrdinalSyntax.fold]
    by_cases h : atom s <;> simp [children,assemble,atom] at h ⊢ <;> simp_all [ordinalCode]

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms := by
  have hs : Primrec (fun p : Nat×Nat×Nat => sourceCode p.1 p.2.1 p.2.2) :=
    source_swapped_primitive.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))
  have ho : Primrec (fun p : Nat×Nat×Nat => ordinalCode p.1 p.2.1 p.2.2) :=
    ordinal_paired_primitive.comp ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))
  refine ⟨index_primitive,hs,ho,?_⟩
  have hvec : Primrec (fun p : (Nat×Nat)×List Nat => vectorCode p.1.1 p.1.2 p.2) :=
    Primrec.list_map Primrec.snd
      (ordinal_paired_primitive.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  exact hvec.comp ((Primrec.fst.pair (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd))
end LogicLineages.OrdinalComparison.Source.SelectedBinderCode.Proof
