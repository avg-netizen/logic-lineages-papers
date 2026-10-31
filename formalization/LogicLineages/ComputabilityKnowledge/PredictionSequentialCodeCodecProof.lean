module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodecTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodec

private theorem fold_node {α : Type} (leaf : Nat → α) (branch : Nat → α → α → α)
    (a b tag : Nat) (ht : 3 ≤ tag ∧ tag ≤ 6) :
    fold leaf branch (8 * Nat.pair a b + tag) = branch tag (fold leaf branch a) (fold leaf branch b) := by
  have hm : (8 * Nat.pair a b + tag) % 8 = tag := by omega
  have hd : (8 * Nat.pair a b + tag) / 8 = Nat.pair a b := by omega
  rw [fold]
  simp only [hm, hd, Nat.unpair_pair]
  rw [dif_neg (by omega)]

theorem foldCorrect : Targets.FoldCorrect := by
  intro α leaf branch c
  induction c with
  | zero' => simp [code, termFold, fold]
  | succ => simp [code, termFold, fold]
  | tail => simp [code, termFold, fold]
  | cons a b iha ihb => rw [code, fold_node leaf branch _ _ 3 (by omega), iha, ihb]; rfl
  | comp a b iha ihb => rw [code, fold_node leaf branch _ _ 4 (by omega), iha, ihb]; rfl
  | case a b iha ihb => rw [code, fold_node leaf branch _ _ 5 (by omega), iha, ihb]; rfl
  | fix a ih => rw [code, fold_node leaf branch _ _ 6 (by omega), ih]; simp [fold, termFold]

theorem roundtrip : Targets.Roundtrip := by
  intro c
  unfold decode
  rw [foldCorrect]
  induction c <;> simp_all [termFold, leafCode, branchCode]

theorem foldPrimitiveRecursive : Targets.FoldPrimitiveRecursive := by
  intro α inst leaf branch hleaf hbranch
  let atom : Nat → Prop := fun n => n%8<3 ∨ n%8=7
  let children : Nat → List Nat := fun n => if atom n then [] else [(n/8).unpair.1, (n/8).unpair.2]
  let assemble : Nat → List α → Option α := fun n rs => some
    (if atom n then leaf n else branch (n%8) (rs.getD 0 (leaf 0)) (rs.getD 1 (leaf 0)))
  have hm : Primrec (fun n : Nat => n%8) := Primrec.nat_mod.comp Primrec.id (Primrec.const 8)
  have hd : Primrec (fun n : Nat => n/8) := Primrec.nat_div.comp Primrec.id (Primrec.const 8)
  have hatom : PrimrecPred atom :=
    (Primrec.nat_lt.comp hm (Primrec.const 3)).or (Primrec.eq.comp hm (Primrec.const 7))
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

private theorem map_fold {α β : Type} (f : α → β) (leaf : Nat → α)
    (branch : Nat → α → α → α) (leaf' : Nat → β) (branch' : Nat → β → β → β)
    (hl : ∀ n, f (leaf n) = leaf' n)
    (hb : ∀ n a b, f (branch n a b) = branch' n (f a) (f b)) (n : Nat) :
    f (fold leaf branch n) = fold leaf' branch' n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [fold, fold]
    split
    · exact hl n
    · rename_i hn
      have hpos : 0 < n := by omega
      have hd := Nat.div_lt_self hpos (show 1 < 8 by decide)
      rw [hb, ih _ ((Nat.unpair_left_le _).trans_lt hd), ih _ ((Nat.unpair_right_le _).trans_lt hd)]

theorem normalizationPrimitiveRecursive : Targets.NormalizationPrimitiveRecursive := by
  let leaf : Nat → Nat := fun n => if n = 1 then 1 else if n = 2 then 2 else 0
  let branch : Nat → Nat → Nat → Nat := fun n a b =>
    if n = 3 then 8 * Nat.pair a b + 3 else if n = 4 then 8 * Nat.pair a b + 4
    else if n = 5 then 8 * Nat.pair a b + 5 else 8 * Nat.pair a 0 + 6
  have hl : Primrec leaf := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 1)) (Primrec.const 1)
    (Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 2)) (Primrec.const 2) (Primrec.const 0))
  have hb : Primrec (fun p : Nat × Nat × Nat => branch p.1 p.2.1 p.2.2) := by
    have he (k : Nat) := Primrec.eq.comp (Primrec.fst (α := Nat) (β := Nat × Nat)) (Primrec.const k)
    have hp : Primrec (fun p : Nat × Nat × Nat => Nat.pair p.2.1 p.2.2) := Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
    have hn (k : Nat) := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8) hp) (Primrec.const k)
    have hf : Primrec (fun p : Nat × Nat × Nat => 8 * Nat.pair p.2.1 0 + 6) := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
      (Primrec₂.natPair.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))) (Primrec.const 6)
    exact Primrec.ite (he 3) (hn 3) (Primrec.ite (he 4) (hn 4) (Primrec.ite (he 5) (hn 5) hf))
  apply (foldPrimitiveRecursive Nat leaf branch hl hb).of_eq
  intro n
  exact (map_fold code leafCode branchCode leaf branch
    (by intro n; dsimp [leafCode, leaf]; split_ifs <;> rfl)
    (by intro n a b; dsimp [branchCode, branch]; split_ifs <;> rfl) n).symm

instance codePrimcodable : Primcodable Code where
  encode := code
  decode := fun n => some (decode n)
  encodek := fun c => congrArg some (roundtrip c)
  prim := by
    have h := Primrec.nat_iff.mp (Primrec.succ.comp normalizationPrimitiveRecursive)
    exact h.of_eq (fun n => rfl)

theorem actualPrimcodable : Targets.ActualPrimcodable := ⟨codePrimcodable, rfl⟩
end LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodec
