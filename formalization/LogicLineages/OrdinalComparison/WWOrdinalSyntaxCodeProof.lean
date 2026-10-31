module
public import LogicLineages.OrdinalComparison.WWOrdinalSyntaxCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OrdinalSyntax

private theorem fold_node {α : Type} (leaf : Nat → α) (branch : Nat → α → α → α)
    (a b tag : Nat) (ht : 4 ≤ tag ∧ tag ≤ 6) :
    fold leaf branch (8 * Nat.pair a b + tag) = branch tag (fold leaf branch a) (fold leaf branch b) := by
  have hm : (8 * Nat.pair a b + tag) % 8 = tag := by omega
  have hd : (8 * Nat.pair a b + tag) / 8 = Nat.pair a b := by omega
  rw [fold]
  simp only [hm, hd, Nat.unpair_pair]
  rw [dif_neg (by omega)]

theorem ordinalSyntaxFoldCorrect : Targets.OrdinalSyntaxFoldCorrect := by
  intro ι α index leaf branch t
  induction t with
  | zero => simp [code, termFold, fold]
  | one => simp [code, termFold, fold]
  | omega => simp [code, termFold, fold]
  | var x =>
    simp only [code, termFold]
    rw [fold]
    have hm : (8 * index x + 3) % 8 = 3 := by omega
    simp [hm]
  | add a b iha ihb => rw [code, fold_node leaf branch _ _ 4 (by omega), iha, ihb]; rfl
  | emul a b iha ihb => rw [code, fold_node leaf branch _ _ 5 (by omega), iha, ihb]; rfl
  | collapse a b iha ihb => rw [code, fold_node leaf branch _ _ 6 (by omega), iha, ihb]; rfl

theorem ordinalSyntaxFoldPrimitiveRecursive : Targets.OrdinalSyntaxFoldPrimitiveRecursive := by
  intro α inst leaf branch hleaf hbranch
  let atom : Nat → Prop := fun n => n%8<4 ∨ n%8=7
  let children : Nat → List Nat := fun n => if atom n then [] else [(n/8).unpair.1, (n/8).unpair.2]
  let assemble : Nat → List α → Option α := fun n rs => some
    (if atom n then leaf n else branch (n%8) (rs.getD 0 (leaf 0)) (rs.getD 1 (leaf 0)))
  have hm : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hd : Primrec (fun n : Nat => n/8) := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
  have hatom : PrimrecPred atom :=
    (Primrec.nat_lt.comp hm (Primrec.const 4)).or (Primrec.eq.comp hm (Primrec.const 7))
  have hl := Primrec.fst.comp (Primrec.unpair.comp hd)
  have hr := Primrec.snd.comp (Primrec.unpair.comp hd)
  have hc : Primrec children := Primrec.ite hatom (Primrec.const [])
    (Primrec.list_cons.comp hl (Primrec.list_cons.comp hr (Primrec.const [])))
  have ha : Primrec₂ assemble := by
    have hg (k : Nat) : Primrec (fun p : Nat × List α => p.2.getD k (leaf 0)) :=
      (Primrec.list_getD (leaf 0)).comp Primrec.snd (Primrec.const k)
    exact Primrec.option_some.comp (Primrec.ite (hatom.comp Primrec.fst)
      (hleaf.comp Primrec.fst)
      (hbranch.comp ((hm.comp Primrec.fst).pair ((hg 0).pair (hg 1)))))
  apply Primrec.nat_omega_rec' (fold leaf branch) Primrec.id hc ha
  · intro n t ht
    by_cases h : atom n
    · simp [children, h] at ht
    have hn : 0<n := by simp only [atom] at h; omega
    have hdiv := Nat.div_lt_self hn (show 1<8 by decide)
    simp only [children, if_neg h, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact (Nat.unpair_left_le _).trans_lt hdiv
    · exact (Nat.unpair_right_le _).trans_lt hdiv
  · intro n
    rw [fold]
    by_cases h : atom n <;> simp [children, assemble, atom] at h ⊢ <;> simp_all
end LogicLineages.OrdinalComparison.Source.OrdinalSyntax
