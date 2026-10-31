module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxBoxTargets
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxSumProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem boxNodePrim {α : Type*} [Primcodable α] {t a b : α → Nat}
    (ht : Primrec t) (ha : Primrec a) (hb : Primrec b) :
    Primrec (fun x => node (t x) (a x) (b x)) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp ha hb)) ht

private theorem positivePrim :
    Primrec (fun p : Nat × List Nat × List Nat × Nat => boxPositive p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let children : (Nat × List Nat × List Nat × Nat) → List (Nat × List Nat × List Nat × Nat) :=
    fun p => if p.2.2.2 ≤ p.1 then [(p.1, p.2.1, p.2.2.1, p.2.2.2+1)] else []
  let assemble : (Nat × List Nat × List Nat × Nat) → List Nat → Option Nat :=
    fun p rs => some (if p.2.2.2 ≤ p.1 then
      node 5 (rs.getD 0 0) (node 4 (p.2.1.getD p.2.2.2 0) (p.2.2.1.getD p.2.2.2 0))
      else p.2.1.getD p.2.2.2 0)
  have hn : Primrec (fun p : Nat × List Nat × List Nat × Nat => p.1) := Primrec.fst
  have hf : Primrec (fun p : Nat × List Nat × List Nat × Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hg : Primrec (fun p : Nat × List Nat × List Nat × Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun p : Nat × List Nat × List Nat × Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hcond := Primrec.nat_le.comp hi hn
  have hchildren : Primrec children := Primrec.ite hcond
    (Primrec.list_cons.comp (hn.pair (hf.pair (hg.pair (Primrec.succ.comp hi)))) (Primrec.const []))
    (Primrec.const [])
  have hassemble : Primrec₂ assemble := by
    have hp : Primrec (fun p : (Nat × List Nat × List Nat × Nat) × List Nat => p.1) := Primrec.fst
    have ha := (Primrec.list_getD 0).comp (hf.comp hp) (hi.comp hp)
    have hb := (Primrec.list_getD 0).comp (hg.comp hp) (hi.comp hp)
    exact Primrec.option_some.comp (Primrec.ite (hcond.comp Primrec.fst)
      (boxNodePrim (Primrec.const 5)
        ((Primrec.list_getD 0).comp Primrec.snd (Primrec.const 0))
        (boxNodePrim (Primrec.const 4) ha hb)) ha)
  apply Primrec.nat_omega_rec'
    (fun p : Nat × List Nat × List Nat × Nat => boxPositive p.1 p.2.1 p.2.2.1 p.2.2.2)
    (Primrec.nat_sub.comp (Primrec.succ.comp hn) hi) hchildren hassemble
  · intro p c hc
    by_cases h : p.2.2.2 ≤ p.1
    · simp only [children, if_pos h, List.mem_singleton] at hc
      subst c
      dsimp
      omega
    · simp [children, h] at hc
  · rintro ⟨n, f, g, i⟩
    conv_rhs => rw [boxPositive]
    by_cases h : i ≤ n <;> simp [assemble, children, h]

private theorem tailPrim {α : Type*} [Primcodable α] {n f g : α → Nat}
    (hn : Primrec n) (hf : Primrec f) (hg : Primrec g) :
    Primrec (fun p => boxTail (n p) (f p) (g p)) := by
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0))
    (boxNodePrim (Primrec.const 4) hf hg)
    (boxNodePrim (Primrec.const 4) (boxNodePrim (Primrec.const 4) hf hg)
      (ordinalSyntaxSumOperationsPrimitiveRecursive.2.comp hn (Primrec.const 1)))

theorem ordinalSyntaxBoxOperationsPrimitiveRecursive : Targets.OrdinalSyntaxBoxOperationsPrimitiveRecursive := by
  refine ⟨positivePrim, ?_⟩
  have hr : Primrec (fun p : Nat × Nat × List Nat × List Nat => p.1) := Primrec.fst
  have hn : Primrec (fun p : Nat × Nat × List Nat × List Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun p : Nat × Nat × List Nat × List Nat => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hg : Primrec (fun p : Nat × Nat × List Nat × List Nat => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hbranch : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat =>
      if p.2 = 0 then node 6 (boxPositive p.1.2.1 p.1.2.2.1 p.1.2.2.2 1)
        (boxTail p.1.2.1 (p.1.2.2.1.getD 0 0) (p.1.2.2.2.getD 0 0))
      else boxPositive p.1.2.1 p.1.2.2.1 p.1.2.2.2 p.2) := by
    have hp : Primrec (fun p : (Nat × Nat × List Nat × List Nat) × Nat => p.1) := Primrec.fst
    have hp1 := positivePrim.comp ((hn.comp hp).pair
      ((hf.comp hp).pair ((hg.comp hp).pair (Primrec.const 1))))
    have hpi := positivePrim.comp ((hn.comp hp).pair
      ((hf.comp hp).pair ((hg.comp hp).pair Primrec.snd)))
    have ht := tailPrim (hn.comp hp)
      ((Primrec.list_getD 0).comp (hf.comp hp) (Primrec.const 0))
      ((Primrec.list_getD 0).comp (hg.comp hp) (Primrec.const 0))
    exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
      (boxNodePrim (Primrec.const 6) hp1 ht) hpi
  have h := Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp hr)) hbranch.to₂
  exact h.of_eq (fun p => rfl)
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
