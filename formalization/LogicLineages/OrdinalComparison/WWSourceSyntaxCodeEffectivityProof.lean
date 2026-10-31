module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeEffectivityTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof

theorem parserExact : Targets.ParserExact := by
  intro n m
  cases hd : decode n with
  | none => simp [parseCode,hd]
  | some r =>
      have he := StatementChecks.encodeDecode n r hd
      simp [parseCode,hd,he,eq_comm]

theorem parserPrimitiveRecursive : Targets.ParserPrimitiveRecursive := by
  let children : Nat → List Nat := fun n =>
    if n%8=5 then [(n/8).unpair.1,(n/8).unpair.2]
    else if n%8=6 then [(n/8).unpair.2] else []
  let appAsm : Option Nat → Option Nat → Option Nat := fun a b => do
    let x ← a
    let y ← b
    pure (8*Nat.pair x y+5)
  let lamAsm : Nat → Option Nat → Option Nat := fun a b => b.map (fun y => 8*Nat.pair a y+6)
  let base : Nat → Option Nat := fun n =>
    if n%8=0 then some (8*(n/8))
    else if n%8=1 then if n/8=0 then some 1 else none
    else if n%8=2 then if n/8=0 then some 2 else none
    else if n%8=3 then some (8*(n/8)+3)
    else if n%8=4 then some (8*(n/8)+4) else none
  let assemble : Nat → List (Option Nat) → Option (Option Nat) := fun n rs => some
    (if n%8=5 then appAsm (rs.getD 0 none) (rs.getD 1 none)
    else if n%8=6 then lamAsm (n/8).unpair.1 (rs.getD 0 none) else base n)
  have hn (k : Nat) : Primrec (fun p : Nat×Nat => 8*Nat.pair p.1 p.2+k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) Primrec₂.natPair) (Primrec.const k)
  have happ : Primrec₂ appAsm := by
    have hh : Primrec (fun p : Option Nat × Option Nat =>
        p.1.bind (fun x => p.2.map (fun y => 8*Nat.pair x y+5))) :=
      Primrec.option_bind Primrec.fst
        (Primrec.option_map (Primrec.snd.comp Primrec.fst)
          ((hn 5).comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂
    exact hh.of_eq (fun p => by cases p.1 <;> cases p.2 <;> rfl)
  have hlam : Primrec₂ lamAsm := Primrec.option_map Primrec.snd
    ((hn 6).comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
  have htag : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hpay : Primrec (fun n : Nat => n/8) := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun n : Nat => n%8=k) := Primrec.eq.comp htag (Primrec.const k)
  have hz : PrimrecPred (fun n : Nat => n/8=0) := Primrec.eq.comp hpay (Primrec.const 0)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const [])))
    (Primrec.ite (ht 6) (Primrec.list_cons.comp hr (Primrec.const [])) (Primrec.const []))
  have ha (k : Nat) : Primrec (fun n : Nat => 8*(n/8)+k) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) hpay) (Primrec.const k)
  have hb : Primrec base := Primrec.ite (ht 0)
    (Primrec.option_some.comp (Primrec.nat_mul.comp (Primrec.const 8) hpay))
    (Primrec.ite (ht 1) (Primrec.ite hz (Primrec.const (some 1)) (Primrec.const none))
    (Primrec.ite (ht 2) (Primrec.ite hz (Primrec.const (some 2)) (Primrec.const none))
    (Primrec.ite (ht 3) (Primrec.option_some.comp (ha 3))
    (Primrec.ite (ht 4) (Primrec.option_some.comp (ha 4)) (Primrec.const none)))))
  have hasm : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : Nat×List (Option Nat) => p.2.getD k none) :=
      (Primrec.list_getD (none : Option Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((ht 5).comp Primrec.fst)
      (happ.comp (hg 0) (hg 1))
      (Primrec.ite ((ht 6).comp Primrec.fst) (hlam.comp (hl.comp Primrec.fst) (hg 0)) (hb.comp Primrec.fst)))
  apply Primrec.nat_omega_rec' parseCode Primrec.id hc hasm
  · intro n t hmem
    change t<n
    by_cases h5 : n%8=5
    · have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hmem
      rcases hmem with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : n%8=6
      · have hd : n/8<n := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hmem
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hmem
  · intro n
    change assemble n ((children n).map parseCode) = some ((decode n).map code)
    conv_rhs => rw [decode]
    have ht : n%8=0 ∨ n%8=1 ∨ n%8=2 ∨ n%8=3 ∨ n%8=4 ∨ n%8=5 ∨ n%8=6 ∨ n%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h
    · simp [children,assemble,base,h,code]
    · by_cases hz : n/8=0 <;> simp [children,assemble,base,h,hz,code] <;> omega
    · by_cases hz : n/8=0 <;> simp [children,assemble,base,h,hz,code] <;> omega
    · simp [children,assemble,base,h,code]
    · simp [children,assemble,base,h,code]
    · cases hf : decode (n/8).unpair.1 <;> cases ha : decode (n/8).unpair.2 <;>
        simp [children,assemble,base,h,parseCode,appAsm,hf,ha,code]
    · cases hb : decode (n/8).unpair.2 <;>
        simp [children,assemble,base,h,parseCode,lamAsm,hb,code]
    · simp [children,assemble,base,h]
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof
