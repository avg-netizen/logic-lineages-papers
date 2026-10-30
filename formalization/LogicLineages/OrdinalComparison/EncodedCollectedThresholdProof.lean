module
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdTargets
public import LogicLineages.OrdinalComparison.RawNormCode

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem threshold_step_primrec : Primrec (fun p : Nat × List (Nat × Nat) =>
    encodedCollectedThresholdStep p.1 p.2) := by
  have hn : Primrec (fun p : Nat × List (Nat × Nat) => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat × List (Nat × Nat) => p.2) := Primrec.snd
  have hp := Primrec.unpair.comp (Primrec.pred.comp hn)
  have hk := Primrec.unpair.comp (Primrec.fst.comp hp)
  have hf := Primrec.unpair.comp (Primrec.snd.comp hp)
  have hA := Primrec.unpair.comp (Primrec.snd.comp hk)
  have hAf := Primrec.unpair.comp (Primrec.snd.comp hA)
  have ha := (Primrec.list_getD (0,1)).comp ht (Primrec.snd.comp hAf)
  have hr := (Primrec.list_getD (0,1)).comp ht (Primrec.snd.comp hf)
  have hb := Primrec.nat_add.comp
    (Primrec.nat_add.comp ((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp (Primrec.fst.comp hk))
      (Primrec.fst.comp hA)) (Primrec.fst.comp hAf)
  have hatom := Primrec.ite (Primrec.eq.comp (Primrec.snd.comp hAf) (Primrec.const 0))
    (Primrec.nat_max.comp (Primrec.const 4) (Primrec.nat_add.comp hb (Primrec.const 1)))
    (Primrec.nat_max.comp (Primrec.const 4) (Primrec.nat_max.comp hb
      (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp ha)) (Primrec.const 1))))
  exact Primrec.ite (Primrec.eq.comp hn (Primrec.const 0)) (Primrec.const (0,1))
    ((Primrec.nat_add.comp (Primrec.fst.comp hf) (Primrec.fst.comp hr)).pair
      (Primrec.nat_max.comp hatom (Primrec.nat_max.comp (Primrec.snd.comp ha) (Primrec.snd.comp hr))))

theorem encodedCollectedThresholdDataPrimitiveRecursive : Targets.EncodedCollectedThresholdDataPrimitiveRecursive := by
  have hs : Primrec₂ (fun n : Nat => fun table : List (Nat × Nat) =>
      table ++ [encodedCollectedThresholdStep n table]) :=
    Primrec.list_concat.comp Primrec.snd threshold_step_primrec
  have ht : Primrec encodedCollectedThresholdTable :=
    (Primrec.nat_rec₁ ([] : List (Nat × Nat)) hs).of_eq (by
      intro n
      induction n with
      | zero => rfl
      | succ n ih =>
        change Nat.rec (motive := fun _ => List (Nat × Nat)) []
          (fun k table => table ++ [encodedCollectedThresholdStep k table]) n ++
          [encodedCollectedThresholdStep n (Nat.rec (motive := fun _ => List (Nat × Nat)) []
            (fun k table => table ++ [encodedCollectedThresholdStep k table]) n)] = _
        change Nat.rec (motive := fun _ => List (Nat × Nat)) []
          (fun k table => table ++ [encodedCollectedThresholdStep k table]) n = _ at ih
        rw [ih]
        rfl)
  exact (Primrec.list_getD (0,1)).comp (ht.comp Primrec.succ) Primrec.id

private theorem threshold_tail_lt (rho : NONote) (A : CollectedPositiveNF) (a : Nat)
    (rest : CollectedPositiveTags) : collectedTagsEncode rest < collectedTagsEncode (.cons rho A a rest) := by
  have h1 := Nat.right_le_pair a (collectedTagsEncode rest)
  have h2 := Nat.right_le_pair (collectedTagKey rho A) (Nat.pair a (collectedTagsEncode rest))
  change collectedTagsEncode rest < 1+Nat.pair (collectedTagKey rho A) (Nat.pair a (collectedTagsEncode rest))
  omega

private theorem threshold_arg_lt (rho : NONote) (c b a : Nat)
    (tags rest : CollectedPositiveTags) :
    collectedTagsEncode tags < collectedTagsEncode (.cons rho (.mk c b tags) a rest) := by
  have h1 := Nat.right_le_pair b (collectedTagsEncode tags)
  have h2 := Nat.right_le_pair c (Nat.pair b (collectedTagsEncode tags))
  have h3 := Nat.right_le_pair (rawNoteEncode rho.1) (Nat.pair c (Nat.pair b (collectedTagsEncode tags)))
  have h4 := Nat.left_le_pair (Nat.pair (rawNoteEncode rho.1) (Nat.pair c (Nat.pair b (collectedTagsEncode tags))))
    (Nat.pair a (collectedTagsEncode rest))
  change collectedTagsEncode tags < 1+Nat.pair
    (Nat.pair (rawNoteEncode rho.1) (Nat.pair c (Nat.pair b (collectedTagsEncode tags))))
    (Nat.pair a (collectedTagsEncode rest))
  omega

private theorem threshold_step_correct (tags : CollectedPositiveTags) (table : List (Nat × Nat))
    (ht : ∀ rest : CollectedPositiveTags, collectedTagsEncode rest < collectedTagsEncode tags →
      table.getD (collectedTagsEncode rest) (0,1)=
        (collectedCoefficientSum rest,collectedTagsOneInputThreshold rest)) :
    encodedCollectedThresholdStep (collectedTagsEncode tags) table=
      (collectedCoefficientSum tags,collectedTagsOneInputThreshold tags) := by
  cases tags with
  | nil => rfl
  | cons rho A a rest =>
    cases A with
    | mk c b args =>
      have hr := ht rest (threshold_tail_lt rho (.mk c b args) a rest)
      have ha := ht args (threshold_arg_lt rho c b a args rest)
      simp only [encodedCollectedThresholdStep,collectedTagsEncode,collectedPositiveEncode]
      have hn : 1+Nat.pair (Nat.pair (rawNoteEncode rho.1) (Nat.pair c (Nat.pair b (collectedTagsEncode args))))
          (Nat.pair a (collectedTagsEncode rest)) ≠ 0 := by omega
      simp only [if_neg hn,Nat.add_comm 1 _,Nat.pred_succ,Nat.unpair_pair]
      rw [hr,ha,rawNormCodeCorrect rho.1]
      cases args <;>
        simp [collectedCoefficientSum,collectedTagsOneInputThreshold,collectedOneInputThreshold,
          collectedAtomThreshold,collectedAffineThreshold,collectedNonlinearThreshold,collectedTagsEncode]

private theorem threshold_table_length (n : Nat) : (encodedCollectedThresholdTable n).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodedCollectedThresholdTable,ih]

private theorem threshold_table_correct (n : Nat) :
    ∀ tags : CollectedPositiveTags, collectedTagsEncode tags<n →
      (encodedCollectedThresholdTable n).getD (collectedTagsEncode tags) (0,1)=
        (collectedCoefficientSum tags,collectedTagsOneInputThreshold tags) := by
  induction n with
  | zero => intro tags h; omega
  | succ n ih =>
    intro tags ht
    by_cases heq : collectedTagsEncode tags=n
    · rw [encodedCollectedThresholdTable,List.getD_append_right _ _ _ _ (by rw [threshold_table_length]; omega)]
      rw [threshold_table_length,heq,Nat.sub_self]
      change encodedCollectedThresholdStep n _=_
      simpa only [heq] using threshold_step_correct tags (encodedCollectedThresholdTable n)
        (fun rest hr => ih rest (by omega))
    · rw [encodedCollectedThresholdTable,List.getD_append _ _ _ _ (by rw [threshold_table_length]; omega)]
      exact ih tags (by omega)

theorem encodedCollectedThresholdDataCorrect : Targets.EncodedCollectedThresholdDataCorrect := by
  intro tags
  exact threshold_table_correct (collectedTagsEncode tags+1) tags (Nat.lt_succ_self _)

private theorem nf_threshold_primrec : Primrec encodedCollectedThreshold := by
  exact Primrec.snd.comp
    (encodedCollectedThresholdDataPrimitiveRecursive.comp
      (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))))

private theorem max_fold_primrec (f : Nat → Nat) (hf : Primrec f) :
    Primrec (fun codes : List Nat => codes.foldr (fun n bound => max (f n) bound) 1) := by
  have hh : Primrec₂ (fun (_ : List Nat) (p : Nat × Nat) => max (f p.1) p.2) :=
    Primrec.nat_max.comp (hf.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr (f := fun codes : List Nat => codes)
    (g := fun _ : List Nat => (1 : Nat))
    (h := fun (_ : List Nat) (p : Nat × Nat) => max (f p.1) p.2)
    Primrec.id (Primrec.const 1) hh

private theorem family_threshold_primrec : Primrec encodedCollectedFamilyThreshold :=
  max_fold_primrec encodedCollectedThreshold nf_threshold_primrec

theorem encodedCollectedThresholdPrimitiveRecursive : Targets.EncodedCollectedThresholdPrimitiveRecursive :=
  ⟨nf_threshold_primrec, family_threshold_primrec⟩

theorem encodedCollectedThresholdCorrect : Targets.EncodedCollectedThresholdCorrect := by
  intro A
  cases A with
  | mk c b tags =>
    simp only [encodedCollectedThreshold,collectedPositiveEncode,Nat.unpair_pair]
    rw [encodedCollectedThresholdDataCorrect tags]
    rfl

theorem encodedCollectedFamilyThresholdCorrect : Targets.EncodedCollectedFamilyThresholdCorrect := by
  intro forms
  induction forms with
  | nil => rfl
  | cons A forms ih =>
    change max (encodedCollectedThreshold (collectedPositiveEncode A))
      (encodedCollectedFamilyThreshold (forms.map collectedPositiveEncode)) =
      max (collectedOneInputThreshold A) (collectedFamilyThreshold forms)
    rw [encodedCollectedThresholdCorrect A,ih]

end LogicLineages.OrdinalComparison
