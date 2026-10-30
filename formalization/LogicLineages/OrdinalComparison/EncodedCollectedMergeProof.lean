module
public import LogicLineages.OrdinalComparison.EncodedCollectedMergeTargets
public import LogicLineages.OrdinalComparison.CollectedMergeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem cons_primrec {α : Type} [Primcodable α] {k a r : α → Nat}
    (hk : Primrec k) (ha : Primrec a) (hr : Primrec r) :
    Primrec (fun x => encodedCollectedCons (k x) (a x) (r x)) :=
  Primrec.nat_add.comp (Primrec.const 1) (Primrec₂.natPair.comp hk (Primrec₂.natPair.comp ha hr))

private theorem insert_step_primrec : Primrec
    (fun p : (Nat × Nat) × (Nat × List Nat) =>
      encodedCollectedInsertStep p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hk : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.1.1) := Primrec.fst.comp Primrec.fst
  have ha : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.1.2) := Primrec.snd.comp Primrec.fst
  have hn : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : (Nat × Nat) × (Nat × List Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp := Primrec.unpair.comp (Primrec.pred.comp hn)
  have hold := Primrec.fst.comp hp
  have hfields := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hb := Primrec.fst.comp hfields
  have hr := Primrec.snd.comp hfields
  exact Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) hn
    (Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) (cons_primrec hk ha (Primrec.const 0))
      (Primrec.ite (Primrec.nat_lt.comp hk hold) (cons_primrec hk ha hn)
        (Primrec.ite (Primrec.eq.comp hk hold) (cons_primrec hold (Primrec.nat_add.comp ha hb) hr)
          (cons_primrec hold hb ((Primrec.list_getD 0).comp ht hr)))))

theorem encodedCollectedInsertPrimitiveRecursive : Targets.EncodedCollectedInsertPrimitiveRecursive := by
  have hs : Primrec₂ (fun p : Nat × Nat => fun q : Nat × List Nat =>
      q.2 ++ [encodedCollectedInsertStep p.1 p.2 q.1 q.2]) :=
    Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) insert_step_primrec
  have ht : Primrec₂ (fun p : Nat × Nat => encodedCollectedInsertTable p.1 p.2) :=
    (Primrec.nat_rec (Primrec.const ([] : List Nat)) hs).of_eq (by
      intro p n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedInsertStep p.1 p.2 k table]) n ++
          [encodedCollectedInsertStep p.1 p.2 n
            (Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedInsertStep p.1 p.2 k table]) n)] = _
        change Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedInsertStep p.1 p.2 k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp
    (ht.comp Primrec.fst (Primrec.succ.comp Primrec.snd)) Primrec.snd

private theorem merge_step_primrec : Primrec (fun p : Nat × (Nat × List Nat) =>
    encodedCollectedMergeStep p.1 p.2.1 p.2.2) := by
  have hn : Primrec (fun p : Nat × (Nat × List Nat) => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : Nat × (Nat × List Nat) => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp := Primrec.unpair.comp (Primrec.pred.comp hn)
  have hk := Primrec.fst.comp hp
  have hf := Primrec.unpair.comp (Primrec.snd.comp hp)
  have ha := Primrec.fst.comp hf
  have hr := Primrec.snd.comp hf
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) Primrec.fst
    (encodedCollectedInsertPrimitiveRecursive.comp ((hk.pair ha).pair ((Primrec.list_getD 0).comp ht hr)))

theorem encodedCollectedMergePrimitiveRecursive : Targets.EncodedCollectedMergePrimitiveRecursive := by
  have hs : Primrec₂ (fun r : Nat => fun q : Nat × List Nat =>
      q.2 ++ [encodedCollectedMergeStep r q.1 q.2]) :=
    Primrec.list_concat.comp (Primrec.snd.comp Primrec.snd) merge_step_primrec
  have ht : Primrec₂ encodedCollectedMergeTable :=
    (Primrec.nat_rec (Primrec.const ([] : List Nat)) hs).of_eq (by
      intro r n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedMergeStep r k table]) n ++
          [encodedCollectedMergeStep r n (Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedMergeStep r k table]) n)] = _
        change Nat.rec (motive := fun _ => List Nat) [] (fun k table => table ++ [encodedCollectedMergeStep r k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD 0).comp
    (ht.comp Primrec.snd (Primrec.succ.comp Primrec.fst)) Primrec.fst

theorem encodedCollectedAddPrimitiveRecursive : Targets.EncodedCollectedAddPrimitiveRecursive := by
  have hl : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
  have hr : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
  have hlf := Primrec.unpair.comp (Primrec.snd.comp hl)
  have hrf := Primrec.unpair.comp (Primrec.snd.comp hr)
  exact Primrec₂.natPair.comp
    (Primrec.nat_add.comp (Primrec.fst.comp hl) (Primrec.fst.comp hr))
    (Primrec₂.natPair.comp
      (Primrec.nat_add.comp (Primrec.fst.comp hlf) (Primrec.fst.comp hrf))
      (encodedCollectedMergePrimitiveRecursive.comp (Primrec.snd.comp hlf) (Primrec.snd.comp hrf)))

private theorem tag_tail_code_lt (rho : NONote) (A : CollectedPositiveNF) (a : Nat)
    (rest : CollectedPositiveTags) :
    collectedTagsEncode rest<collectedTagsEncode (.cons rho A a rest) := by
  have h1 := Nat.right_le_pair a (collectedTagsEncode rest)
  have h2 := Nat.right_le_pair (collectedTagKey rho A) (Nat.pair a (collectedTagsEncode rest))
  change collectedTagsEncode rest < 1+Nat.pair (collectedTagKey rho A) (Nat.pair a (collectedTagsEncode rest))
  omega

private theorem insert_step_correct (rho : NONote) (A : CollectedPositiveNF) (a : Nat)
    (tags : CollectedPositiveTags) (table : List Nat)
    (ht : ∀ rest : CollectedPositiveTags, collectedTagsEncode rest<collectedTagsEncode tags →
      table.getD (collectedTagsEncode rest) 0=collectedTagsEncode (collectedTagInsert rho A a rest)) :
    encodedCollectedInsertStep (collectedTagKey rho A) a (collectedTagsEncode tags) table=
      collectedTagsEncode (collectedTagInsert rho A a tags) := by
  cases tags with
  | nil =>
    by_cases ha : a=0 <;>
      simp [encodedCollectedInsertStep,collectedTagInsert,collectedTagsEncode,ha,encodedCollectedCons,collectedTagKey]
  | cons sigma B b rest =>
    have hrest := ht rest (tag_tail_code_lt sigma B b rest)
    by_cases ha : a=0
    · simp [encodedCollectedInsertStep,collectedTagInsert,ha]
    by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
    · simp only [collectedTagKey] at hl
      simp [encodedCollectedInsertStep,collectedTagInsert,collectedTagsEncode,encodedCollectedCons,
        collectedTagKey,Nat.add_comm,ha,hl]
    by_cases he : collectedTagKey rho A=collectedTagKey sigma B
    · simp only [collectedTagKey,Nat.pair_eq_pair] at hl he
      simp [encodedCollectedInsertStep,collectedTagInsert,collectedTagsEncode,encodedCollectedCons,
        collectedTagKey,Nat.add_comm,ha,hl,he]
    · simp only [collectedTagKey,Nat.pair_eq_pair] at hl he
      simp [encodedCollectedInsertStep,collectedTagInsert,collectedTagsEncode,encodedCollectedCons,
        collectedTagKey,Nat.add_comm,ha,hl,he,hrest]
      simpa only [List.getD_eq_getElem?_getD] using hrest

private theorem insert_table_length (key a n : Nat) :
    (encodedCollectedInsertTable key a n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedCollectedInsertTable,ih]

private theorem insert_table_correct (rho : NONote) (A : CollectedPositiveNF) (a n : Nat) :
    ∀ tags : CollectedPositiveTags, collectedTagsEncode tags<n →
      (encodedCollectedInsertTable (collectedTagKey rho A) a n).getD (collectedTagsEncode tags) 0=
        collectedTagsEncode (collectedTagInsert rho A a tags) := by
  induction n with
  | zero => intro tags h; omega
  | succ n ih =>
    intro tags ht
    by_cases heq : collectedTagsEncode tags=n
    · rw [encodedCollectedInsertTable,List.getD_append_right _ _ _ _ (by rw [insert_table_length]; omega)]
      rw [insert_table_length,heq,Nat.sub_self]
      change encodedCollectedInsertStep _ a n _=_
      simpa only [heq] using insert_step_correct rho A a tags
        (encodedCollectedInsertTable (collectedTagKey rho A) a n) (fun rest hr => ih rest (by omega))
    · rw [encodedCollectedInsertTable,List.getD_append _ _ _ _ (by rw [insert_table_length]; omega)]
      exact ih tags (by omega)

theorem encodedCollectedInsertCorrect : Targets.EncodedCollectedInsertCorrect := by
  intro rho A a tags
  exact insert_table_correct rho A a (collectedTagsEncode tags+1) tags (Nat.lt_succ_self _)

private theorem merge_table_length (right n : Nat) :
    (encodedCollectedMergeTable right n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedCollectedMergeTable,ih]

private theorem merge_step_correct (left right : CollectedPositiveTags) (table : List Nat)
    (ht : ∀ rest : CollectedPositiveTags, collectedTagsEncode rest<collectedTagsEncode left →
      table.getD (collectedTagsEncode rest) 0=collectedTagsEncode (collectedTagsMerge rest right)) :
    encodedCollectedMergeStep (collectedTagsEncode right) (collectedTagsEncode left) table=
      collectedTagsEncode (collectedTagsMerge left right) := by
  cases left with
  | nil => rfl
  | cons rho A a rest =>
    have hrest := ht rest (tag_tail_code_lt rho A a rest)
    simp only [encodedCollectedMergeStep,collectedTagsEncode]
    have hne : 1+Nat.pair (collectedTagKey rho A) (Nat.pair a (collectedTagsEncode rest))≠0 := by omega
    simp only [if_neg hne,Nat.add_comm 1 _,Nat.pred_succ,Nat.unpair_pair]
    rw [hrest]
    exact encodedCollectedInsertCorrect rho A a (collectedTagsMerge rest right)

private theorem merge_table_correct (right : CollectedPositiveTags) (n : Nat) :
    ∀ left : CollectedPositiveTags, collectedTagsEncode left<n →
      (encodedCollectedMergeTable (collectedTagsEncode right) n).getD (collectedTagsEncode left) 0=
        collectedTagsEncode (collectedTagsMerge left right) := by
  induction n with
  | zero => intro left h; omega
  | succ n ih =>
    intro left hl
    by_cases heq : collectedTagsEncode left=n
    · rw [encodedCollectedMergeTable,List.getD_append_right _ _ _ _ (by rw [merge_table_length]; omega)]
      rw [merge_table_length,heq,Nat.sub_self]
      change encodedCollectedMergeStep _ n _=_
      simpa only [heq] using merge_step_correct left right
        (encodedCollectedMergeTable (collectedTagsEncode right) n) (fun rest hr => ih rest (by omega))
    · rw [encodedCollectedMergeTable,List.getD_append _ _ _ _ (by rw [merge_table_length]; omega)]
      exact ih left (by omega)

theorem encodedCollectedMergeCorrect : Targets.EncodedCollectedMergeCorrect := by
  intro left right
  exact merge_table_correct right (collectedTagsEncode left+1) left (Nat.lt_succ_self _)

theorem encodedCollectedAddCorrect : Targets.EncodedCollectedAddCorrect := by
  intro A B
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      simp only [encodedCollectedAdd,collectedPositiveEncode,Nat.unpair_pair,collectedPositiveAdd]
      rw [encodedCollectedMergeCorrect tags rest]

end LogicLineages.OrdinalComparison
