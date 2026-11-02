module
public import LogicLineages.OrdinalComparison.SourceAnnotationCodeTargets
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Proof

private theorem mod_tag (a tag : Nat) (h : tag<4) : (4*a+tag)%4=tag := by omega
private theorem div_tag (a tag : Nat) (h : tag<4) : (4*a+tag)/4=a := by omega

theorem fold_free (atom : Nat → Nat → Nat → Nat) (add collapse : Nat → Nat → Nat → Nat)
    (ctx payload : Nat) : fold atom add collapse ctx (4*payload) = atom ctx 0 payload := by
  rw [fold]
  simp

theorem fold_tracked (atom : Nat → Nat → Nat → Nat) (add collapse : Nat → Nat → Nat → Nat)
    (ctx : Nat) : fold atom add collapse ctx 1 = atom ctx 1 0 := by
  rw [fold]
  simp

theorem fold_add (atom : Nat → Nat → Nat → Nat) (add collapse : Nat → Nat → Nat → Nat)
    (ctx a b : Nat) : fold atom add collapse ctx (4*Nat.pair a b+2) =
      add ctx (fold atom add collapse ctx a) (fold atom add collapse ctx b) := by
  rw [fold]
  simp [mod_tag _ 2 (by decide),div_tag _ 2 (by decide)]

theorem fold_collapse (atom : Nat → Nat → Nat → Nat) (add collapse : Nat → Nat → Nat → Nat)
    (ctx op tail : Nat) : fold atom add collapse ctx (4*Nat.pair op tail+3) =
      collapse ctx op (fold atom add collapse ctx tail) := by
  rw [fold]
  simp [mod_tag _ 3 (by decide),div_tag _ 3 (by decide)]

theorem fold_primitive (atom add collapse : Nat → Nat → Nat → Nat)
    (hatom : Primrec (fun p : Nat × Nat × Nat => atom p.1 p.2.1 p.2.2))
    (hadd : Primrec (fun p : Nat × Nat × Nat => add p.1 p.2.1 p.2.2))
    (hcollapse : Primrec (fun p : Nat × Nat × Nat => collapse p.1 p.2.1 p.2.2)) :
    Primrec₂ (fold atom add collapse) := by
  let children : (Nat×Nat) → List (Nat×Nat) := fun s =>
    if s.2%4=2 then [(s.1,(s.2/4).unpair.1),(s.1,(s.2/4).unpair.2)]
    else if s.2%4=3 then [(s.1,(s.2/4).unpair.2)] else []
  let assemble : (Nat×Nat) → List Nat → Option Nat := fun s rs => some
    (if s.2%4=2 then add s.1 (rs.getD 0 0) (rs.getD 1 0)
    else if s.2%4=3 then collapse s.1 (s.2/4).unpair.1 (rs.getD 0 0)
    else atom s.1 (s.2%4) (s.2/4))
  have htag : Primrec (fun s : Nat×Nat => s.2%4) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 4)
  have hpay : Primrec (fun s : Nat×Nat => s.2/4) := Primrec.nat_div.comp Primrec.snd (Primrec.const 4)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : Nat×Nat => s.2%4=k) := Primrec.eq.comp htag (Primrec.const k)
  have hc : Primrec children := Primrec.ite (ht 2)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 3) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])) (Primrec.const []))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat×Nat)×List Nat => p.2.getD k 0) :=
      (Primrec.list_getD (0 : Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((ht 2).comp Primrec.fst)
      (hadd.comp ((Primrec.fst.comp Primrec.fst).pair ((hg 0).pair (hg 1))))
      (Primrec.ite ((ht 3).comp Primrec.fst)
        (hcollapse.comp ((Primrec.fst.comp Primrec.fst).pair ((hl.comp Primrec.fst).pair (hg 0))))
        (hatom.comp ((Primrec.fst.comp Primrec.fst).pair ((htag.comp Primrec.fst).pair (hpay.comp Primrec.fst))))))
  apply Primrec.nat_omega_rec' (fun s : Nat×Nat => fold atom add collapse s.1 s.2) Primrec.snd hc ha
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
    conv_rhs => rw [fold]
    have ht : s.2%4=0 ∨ s.2%4=1 ∨ s.2%4=2 ∨ s.2%4=3 := by omega
    rcases ht with h|h|h|h <;> simp [children,assemble,h]
end LogicLineages.OrdinalComparison.Source.SourceAnnotationCode.Proof
