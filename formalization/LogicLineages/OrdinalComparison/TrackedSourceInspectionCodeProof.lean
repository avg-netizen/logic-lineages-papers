module
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeSemanticProof
public import LogicLineages.OrdinalComparison.WWGroundClosingCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode.Proof

private theorem occurs_primitive : Primrec₂ occursCode := by
  let children : (Nat×Nat) → List (Nat×Nat) := fun s =>
    if s.2%8=5 then [(s.1,(s.2/8).unpair.1),(s.1,(s.2/8).unpair.2)]
    else if s.2%8=6 then [(s.1+1,(s.2/8).unpair.2)] else []
  let assemble : (Nat×Nat) → List Bool → Option Bool := fun s rs => some
    (if s.2%8=0 then decide (s.2/8=s.1)
    else if s.2%8=5 then rs.getD 0 false || rs.getD 1 false
    else if s.2%8=6 then rs.getD 0 false else false)
  have htag : Primrec (fun s : Nat×Nat => s.2%8) := Primrec.nat_mod.comp Primrec.snd (Primrec.const 8)
  have hpay : Primrec (fun s : Nat×Nat => s.2/8) := Primrec.nat_div.comp Primrec.snd (Primrec.const 8)
  have hl := Primrec.fst.comp (Primrec.unpair.comp hpay)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hpay)
  have ht (k : Nat) : PrimrecPred (fun s : Nat×Nat => s.2%8=k) := Primrec.eq.comp htag (Primrec.const k)
  have hc : Primrec children := Primrec.ite (ht 5)
    (Primrec.list_cons.comp (Primrec.fst.pair hl) (Primrec.list_cons.comp (Primrec.fst.pair hr) (Primrec.const [])))
    (Primrec.ite (ht 6) (Primrec.list_cons.comp ((Primrec.succ.comp Primrec.fst).pair hr) (Primrec.const [])) (Primrec.const []))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : (Nat×Nat)×List Bool => p.2.getD k false) :=
      (Primrec.list_getD false).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite ((ht 0).comp Primrec.fst)
      ((Primrec.eq.comp hpay Primrec.fst).decide.comp Primrec.fst)
      (Primrec.ite ((ht 5).comp Primrec.fst) (Primrec.or.comp (hg 0) (hg 1))
      (Primrec.ite ((ht 6).comp Primrec.fst) (hg 0) (Primrec.const false))))
  apply Primrec.nat_omega_rec' (fun s : Nat×Nat => occursCode s.1 s.2) Primrec.snd hc ha
  · intro s t hm
    change t.2<s.2
    by_cases h5 : s.2%8=5
    · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
      simp only [children,if_pos h5,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl
      · exact (Nat.unpair_left_le _).trans_lt hd
      · exact (Nat.unpair_right_le _).trans_lt hd
    · by_cases h6 : s.2%8=6
      · have hd : s.2/8<s.2 := Nat.div_lt_self (by omega) (by decide)
        simp only [children,if_neg h5,if_pos h6,List.mem_singleton] at hm
        subst t
        exact (Nat.unpair_right_le _).trans_lt hd
      · simp [children,h5,h6] at hm
  · intro s
    conv_rhs => rw [occursCode]
    have ht : s.2%8=0 ∨ s.2%8=1 ∨ s.2%8=2 ∨ s.2%8=3 ∨ s.2%8=4 ∨ s.2%8=5 ∨ s.2%8=6 ∨ s.2%8=7 := by omega
    rcases ht with h|h|h|h|h|h|h|h <;> simp [children,assemble,h]

private theorem arity_primitive : Primrec arityCode := by
  let children : Nat → List Nat := fun n => if n=0 then [] else [(n-1).unpair.2]
  let assemble : Nat → List (Option Nat) → Option (Option Nat) := fun n rs => some
    (if n=0 then some 0 else if (n-1).unpair.1=0 then (rs.getD 0 none).map Nat.succ else none)
  have hz : PrimrecPred (fun n : Nat => n=0) := Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hp := Primrec.unpair.comp (Primrec.nat_sub.comp Primrec.id (Primrec.const 1))
  have hl := Primrec.fst.comp hp
  have hr := Primrec.snd.comp hp
  have hc : Primrec children := Primrec.ite hz (Primrec.const [])
    (Primrec.list_cons.comp hr (Primrec.const []))
  have ha : Primrec₂ assemble := by
    have hg : Primrec (fun p : Nat×List (Option Nat) => p.2.getD 0 none) :=
      (Primrec.list_getD (none : Option Nat)).comp Primrec.snd (Primrec.const 0)
    exact Primrec.option_some.comp (Primrec.ite (hz.comp Primrec.fst) (Primrec.const (some 0))
      (Primrec.ite ((Primrec.eq.comp hl (Primrec.const 0)).comp Primrec.fst)
        (Primrec.option_map hg (Primrec.succ.comp Primrec.snd).to₂) (Primrec.const none)))
  apply Primrec.nat_omega_rec' arityCode Primrec.id hc ha
  · intro n t hm
    change t<n
    by_cases hn : n=0
    · simp [children,hn] at hm
    simp only [children,if_neg hn,List.mem_singleton] at hm
    subst t
    have := Nat.unpair_right_le (n-1)
    omega
  · intro n
    conv_rhs => rw [arityCode]
    by_cases hn : n=0 <;> simp [children,assemble,hn]

theorem primitiveRecursiveAlgorithms : Targets.PrimitiveRecursiveAlgorithms :=
  ⟨occurs_primitive,arity_primitive⟩
end LogicLineages.OrdinalComparison.Source.TrackedSourceInspectionCode.Proof
