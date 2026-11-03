module
public import LogicLineages.OrdinalComparison.SourceCarrierMapCodeSemanticProof
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.Proof

private theorem fixed_primitive (fresh : Bool) : Primrec₂ (mapCode fresh) := by
  have hvar : Primrec (fun s : Nat × Nat => variableCode fresh s.1 s.2) := by
    have hl : PrimrecPred (fun s : Nat × Nat => s.2 < s.1) := Primrec.nat_lt.comp Primrec.snd Primrec.fst
    have he : PrimrecPred (fun s : Nat × Nat => s.2 = s.1) := Primrec.eq.comp Primrec.snd Primrec.fst
    have hi : Primrec (fun s : Nat × Nat => 8*s.2) := Primrec.nat_mul.comp (Primrec.const 8) Primrec.snd
    cases fresh with
    | false =>
      simp only [variableCode,Bool.false_eq_true,↓reduceIte]
      exact Primrec.ite hl hi (Primrec.ite he (Primrec.const 1)
        (Primrec.nat_mul.comp (Primrec.const 8) (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1))))
    | true =>
      simp only [variableCode,↓reduceIte]
      exact Primrec.ite hl hi (Primrec.ite he hi
        (Primrec.nat_mul.comp (Primrec.const 8) (Primrec.succ.comp Primrec.snd)))
  let children : (Nat×Nat) → List (Nat×Nat) := fun s =>
    if s.2%8=5 then [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
    else if s.2%8=6 then [(s.1+1,(s.2/8).unpair.2)] else []
  let base : (Nat×Nat) → Nat := fun s =>
    if s.2%8=0 then variableCode fresh s.1 (s.2/8)
    else if s.2%8=1 then 1
    else if s.2%8=2 then if s.2/8=0 then 2 else 1
    else if s.2%8=3 then s.2
    else if s.2%8=4 then s.2 else 1
  let assemble : (Nat×Nat) → List Nat → Option Nat := fun s rs => some
    (if s.2%8=5 then 8*Nat.pair (rs.getD 0 1) (rs.getD 1 1)+5
    else if s.2%8=6 then 8*Nat.pair (s.2/8).unpair.1 (rs.getD 0 1)+6
    else base s)
  have hn (k : Nat) : Primrec (fun p : Nat×Nat => 8*Nat.pair p.1 p.2+k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const k)
  have htag : Primrec (fun s : Nat×Nat => s.2%8) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  have hpay : Primrec (fun s : Nat×Nat => s.2/8) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : Nat×Nat => s.2%8=k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hz : PrimrecPred (fun s : Nat×Nat => s.2/8=0) :=
    Primrec.eq.comp hpay (Primrec.const 0)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 6)
      (Primrec.list_cons.comp ((Primrec.succ.comp Primrec.fst).pair hr) (Primrec.const []))
      (Primrec.const []))
  have hb : Primrec base := Primrec.ite (ht 0)
    (hvar.comp (Primrec.fst.pair hpay))
    (Primrec.ite (ht 1) (Primrec.const 1)
    (Primrec.ite (ht 2) (Primrec.ite hz (Primrec.const 2) (Primrec.const 1))
    (Primrec.ite (ht 3) Primrec.snd
    (Primrec.ite (ht 4) Primrec.snd (Primrec.const 1)))))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat×Nat)×List Nat => p.2.getD k 1) :=
      (Primrec.list_getD (1 : Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((ht 5).comp Primrec.fst)
      ((hn 5).comp ((hg 0).pair (hg 1)))
      (Primrec.ite ((ht 6).comp Primrec.fst)
        ((hn 6).comp ((hl.comp Primrec.fst).pair (hg 0))) (hb.comp Primrec.fst)))
  apply Primrec.nat_omega_rec' (fun s : Nat×Nat => mapCode fresh s.1 s.2) Primrec.snd hc ha
  · intro s t hmem
    change t.2 < s.2
    by_cases h5 : s.2%8=5
    · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2%8=6
      · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hmem
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hmem
  · intro s
    conv_rhs => rw [mapCode]
    have ht : s.2%8=0 ∨ s.2%8=1 ∨ s.2%8=2 ∨ s.2%8=3 ∨ s.2%8=4 ∨ s.2%8=5 ∨ s.2%8=6 ∨ s.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,base,h]

theorem primitiveRecursive : Targets.PrimitiveRecursive := by
  have h : Primrec (fun p : Bool × Nat × Nat =>
      if p.1 = true then mapCode true p.2.1 p.2.2 else mapCode false p.2.1 p.2.2) :=
    Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const true))
      ((fixed_primitive true).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      ((fixed_primitive false).comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  apply h.of_eq
  intro p
  cases p.1 <;> rfl
end LogicLineages.OrdinalComparison.Source.SourceCarrierMapCode.Proof
