module
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeCheckTargets
public import LogicLineages.OrdinalComparison.WWSourceSyntaxCodeTypesStatementChecks
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof

theorem appResultPrimitiveRecursive : Primrec₂ appResult := by
  let body : Nat × Nat → Option Nat := fun p =>
    if p.1=0 then none else if (p.1-1).unpair.1=p.2 then some (p.1-1).unpair.2 else none
  have hp : Primrec (fun p : Nat×Nat => (p.1-1).unpair) :=
    Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.fst (Primrec.const 1))
  have hb : Primrec body := Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.const none) (Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hp) Primrec.snd)
      (Primrec.option_some.comp (Primrec.snd.comp hp)) (Primrec.const none))
  exact Primrec.option_bind Primrec.fst
    (Primrec.option_bind (Primrec.snd.comp Primrec.fst)
      (hb.comp ((Primrec.snd.comp Primrec.fst).pair Primrec.snd)).to₂).to₂

theorem lamResultPrimitiveRecursive : Primrec₂ (fun σ b : Nat => arrowCode σ b) :=
  StatementChecks.typeConstructorsPrimitiveRecursive.1

theorem checkPrimitiveRecursive : Targets.CheckPrimitiveRecursive := by
  let children : (List Nat×Nat) → List (List Nat×Nat) := fun s =>
    if s.2%8=5 then [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
    else if s.2%8=6 then [((s.2/8).unpair.1::s.1,(s.2/8).unpair.2)] else []
  let base : (List Nat×Nat) → Option Nat := fun s =>
    if s.2%8=0 then s.1[s.2/8]?
    else if s.2%8=1 then if s.2/8=0 then some 0 else none
    else if s.2%8=2 then if s.2/8=0 then some (arrowCode 0 0) else none
    else if s.2%8=3 then some (caseCode (s.2/8))
    else if s.2%8=4 then some (recCode (s.2/8)) else none
  let assemble : (List Nat×Nat) → List (Option Nat) → Option (Option Nat) := fun s rs => some
    (if s.2%8=5 then appResult (rs.getD 0 none) (rs.getD 1 none)
    else if s.2%8=6 then (rs.getD 0 none).map (arrowCode (s.2/8).unpair.1)
    else base s)
  have htag : Primrec (fun s : List Nat×Nat => s.2%8) :=
    Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  have hpay : Primrec (fun s : List Nat×Nat => s.2/8) :=
    Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : List Nat×Nat => s.2%8=k) :=
    Primrec.eq.comp htag (Primrec.const k)
  have hz : PrimrecPred (fun s : List Nat×Nat => s.2/8=0) :=
    Primrec.eq.comp hpay (Primrec.const 0)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair hl)
      (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 6)
      (Primrec.list_cons.comp ((Primrec.list_cons.comp hl Primrec.fst).pair hr) (Primrec.const []))
      (Primrec.const []))
  have hb : Primrec base := Primrec.ite (ht 0) (Primrec.list_getElem?.comp Primrec.fst hpay)
    (Primrec.ite (ht 1) (Primrec.ite hz (Primrec.const (some 0)) (Primrec.const none))
    (Primrec.ite (ht 2) (Primrec.ite hz (Primrec.const (some (arrowCode 0 0))) (Primrec.const none))
    (Primrec.ite (ht 3) (Primrec.option_some.comp (StatementChecks.typeConstructorsPrimitiveRecursive.2.1.comp hpay))
    (Primrec.ite (ht 4) (Primrec.option_some.comp (StatementChecks.typeConstructorsPrimitiveRecursive.2.2.comp hpay))
      (Primrec.const none)))))
  have hm : Primrec₂ (fun σ b => b.map (arrowCode σ) : Nat → Option Nat → Option Nat) :=
    Primrec.option_map Primrec.snd (lamResultPrimitiveRecursive.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (List Nat×Nat)×List (Option Nat) => p.2.getD k none) :=
      (Primrec.list_getD (none : Option Nat)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((ht 5).comp Primrec.fst)
      (appResultPrimitiveRecursive.comp (hg 0) (hg 1))
      (Primrec.ite ((ht 6).comp Primrec.fst) (hm.comp (hl.comp Primrec.fst) (hg 0)) (hb.comp Primrec.fst)))
  apply Primrec.nat_omega_rec' (fun s : List Nat×Nat => check s.1 s.2) Primrec.snd hc ha
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
    conv_rhs => rw [check]
    have ht : s.2%8=0 ∨ s.2%8=1 ∨ s.2%8=2 ∨ s.2%8=3 ∨ s.2%8=4 ∨ s.2%8=5 ∨ s.2%8=6 ∨ s.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,base,h]
end LogicLineages.OrdinalComparison.Source.SyntaxCode.Proof
