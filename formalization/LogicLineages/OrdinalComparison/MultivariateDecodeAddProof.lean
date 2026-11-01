module
public import LogicLineages.OrdinalComparison.MultivariateDictionaryExtensionalityProof
public import LogicLineages.OrdinalComparison.MultivariateCollectedSourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateDirectNormalize

local infixl:65 " ⊞ " => multivariateCollectedAdd
private def C (n : Nat) : MultivariateCollectedNF := .mk n [] .nil

private theorem old_tags_induction {P : CollectedPositiveTags → Prop}
    (nil : P .nil) (cons : ∀ rho A a rest, P rest → P (.cons rho A a rest))
    (tags : CollectedPositiveTags) : P tags := by
  cases tags with
  | nil => exact nil
  | cons rho A a rest => exact cons rho A a rest (old_tags_induction nil cons rest)
termination_by tags

private theorem C_ordered (n : Nat) : MultivariateCollectedRootOrdered (C n) := True.intro

theorem decode_tags_ordered (cap : Nat) (tags : CollectedPositiveTags) :
    MultivariateCollectedRootOrdered (decodeMultivariateCollectedTags cap tags) := by
  cases tags with
  | nil => exact True.intro
  | cons rho A a rest =>
    cases hi : positiveVariableHeadIndex cap rho with
    | none =>
      simp only [decodeMultivariateCollectedTags,hi]
      exact MultivariateDictionary.structural_algebra.1 _ _ (decode_tags_ordered cap rest)
    | some i =>
      simp only [decodeMultivariateCollectedTags,hi]
      exact MultivariateDictionary.structural_algebra.1 _ _ (decode_tags_ordered cap rest)
termination_by tags

theorem decode_ordered (cap : Nat) (A : CollectedPositiveNF) :
    MultivariateCollectedRootOrdered (decodeMultivariateCollected cap A) := by
  cases A with
  | mk c b tags => exact MultivariateDictionary.structural_algebra.1 _ _ (decode_tags_ordered cap tags)

private theorem basis_add (i a b : Nat) :
    multivariateVariableCoefficients i (a+b)=
      multivariateCoefficientAdd (multivariateVariableCoefficients i a) (multivariateVariableCoefficients i b) := by
  by_cases ha : a=0
  · subst a
    simp [multivariateVariableCoefficients,multivariateCoefficientAdd]
  by_cases hb : b=0
  · subst b
    simp only [Nat.add_zero,multivariateVariableCoefficients,if_pos rfl,if_neg ha]
    cases hi : List.replicate i 0 ++ [a] <;> rfl
  have hab : a+b≠0 := by omega
  simp only [multivariateVariableCoefficients,if_neg ha,if_neg hb,if_neg hab]
  induction i with
  | zero => rfl
  | succ i ih =>
    simpa only [List.replicate_succ,List.cons_append,multivariateCoefficientAdd,Nat.zero_add] using
      congrArg (List.cons 0) ih

private noncomputable def entry (cap : Nat) (rho : NONote) (A : CollectedPositiveNF)
    (a : Nat) : MultivariateCollectedNF :=
  match positiveVariableHeadIndex cap rho with
  | some i => .mk 0 (multivariateVariableCoefficients i a) .nil
  | none => .mk 0 [] (multivariateCollectedTagInsert rho (decodeMultivariateCollected cap A) a .nil)

private theorem entry_ordered (cap : Nat) (rho : NONote) (A : CollectedPositiveNF) (a : Nat) :
    MultivariateCollectedRootOrdered (entry cap rho A a) := by
  cases hi : positiveVariableHeadIndex cap rho with
  | some i => simp only [entry,hi,MultivariateCollectedRootOrdered,MultivariateDictionaryOrdered]
  | none =>
    simp only [entry,hi,MultivariateCollectedRootOrdered]
    exact MultivariateDictionary.canonical_insertion.1 _ _ _ .nil True.intro

private theorem entry_zero (cap : Nat) (rho : NONote) (A : CollectedPositiveNF) :
    entry cap rho A 0=C 0 := by
  cases hi : positiveVariableHeadIndex cap rho <;>
    simp [entry,hi,multivariateVariableCoefficients,multivariateCollectedTagInsert,C]

private theorem entry_add (cap : Nat) (rho : NONote) (A : CollectedPositiveNF) (a b : Nat) :
    entry cap rho A (a+b)=entry cap rho A a ⊞ entry cap rho A b := by
  cases hi : positiveVariableHeadIndex cap rho with
  | some i =>
    simp only [entry,hi,multivariateCollectedAdd,basis_add,multivariateCollectedTagsMerge,Nat.add_zero]
  | none =>
    by_cases ha : a=0
    · subst a
      simp [entry,hi,multivariateCollectedTagInsert,multivariateCollectedAdd,
        multivariateCoefficientAdd,multivariateCollectedTagsMerge]
    by_cases hb : b=0
    · subst b
      simp [entry,hi,multivariateCollectedTagInsert,ha,multivariateCollectedAdd,
        multivariateCoefficientAdd,multivariateCollectedTagsMerge]
    have hab : a+b≠0 := by omega
    simp [entry,hi,multivariateCollectedTagInsert,ha,hb,hab,multivariateCollectedAdd,
      multivariateCoefficientAdd,multivariateCollectedTagsMerge]

private theorem raw_single_add (rho : NONote) (A : MultivariateCollectedNF) (a : Nat)
    (B : MultivariateCollectedNF) :
    MultivariateCollectedNF.mk 0 [] (.cons rho A a .nil) ⊞ B=
      MultivariateCollectedNF.mk 0 [] (multivariateCollectedTagInsert rho A a .nil) ⊞ B := by
  cases B with
  | mk c b tags =>
    have hz : multivariateCollectedTagInsert rho A 0 tags=tags := by cases tags <;> rfl
    by_cases ha : a=0 <;>
      simp [multivariateCollectedAdd,multivariateCoefficientAdd,multivariateCollectedTagsMerge,
        multivariateCollectedTagInsert,ha,hz]

private theorem decode_cons (cap : Nat) (rho : NONote) (A : CollectedPositiveNF)
    (a : Nat) (tags : CollectedPositiveTags) :
    decodeMultivariateCollectedTags cap (.cons rho A a tags)=
      entry cap rho A a ⊞ decodeMultivariateCollectedTags cap tags := by
  cases hi : positiveVariableHeadIndex cap rho with
  | some i => simp only [decodeMultivariateCollectedTags,entry,hi]
  | none =>
    simpa only [decodeMultivariateCollectedTags,entry,hi] using
      raw_single_add rho (decodeMultivariateCollected cap A) a (decodeMultivariateCollectedTags cap tags)

private theorem swap_middle (A B D : MultivariateCollectedNF)
    (hA : MultivariateCollectedRootOrdered A) (hB : MultivariateCollectedRootOrdered B)
    (hD : MultivariateCollectedRootOrdered D) : A ⊞ (B ⊞ D)=B ⊞ (A ⊞ D) := by
  rw [← MultivariateDictionary.structural_algebra.2.2.1 A B D hD,
    MultivariateDictionary.structural_algebra.2.1 A B hA hB,
    MultivariateDictionary.structural_algebra.2.2.1 B A D hD]

private theorem decode_insert (cap : Nat) (rho : NONote) (A : CollectedPositiveNF) (a : Nat)
    (tags : CollectedPositiveTags) :
    decodeMultivariateCollectedTags cap (collectedTagInsert rho A a tags)=
      entry cap rho A a ⊞ decodeMultivariateCollectedTags cap tags := by
  induction tags using old_tags_induction with
  | nil =>
    by_cases ha : a=0
    · simp only [collectedTagInsert,if_pos ha,ha,entry_zero]
      exact (MultivariateDictionary.structural_algebra.2.2.2.1 _).symm
    · rw [collectedTagInsert,if_neg ha,decode_cons]
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · rw [collectedTagInsert,if_pos ha,ha,entry_zero]
      exact (MultivariateDictionary.structural_algebra.2.2.2.1 _).symm
    by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
    · rw [collectedTagInsert,if_neg ha,if_pos hl,decode_cons]
    by_cases he : collectedTagKey rho A=collectedTagKey sigma B
    · rcases (collectedPositiveTagIdentity rho sigma A B).mp he with ⟨rfl,rfl⟩
      rw [collectedTagInsert,if_neg ha,if_neg hl,if_pos rfl,decode_cons,entry_add,
        MultivariateDictionary.structural_algebra.2.2.1 _ _ _ (decode_tags_ordered cap rest),decode_cons]
    · rw [collectedTagInsert,if_neg ha,if_neg hl,if_neg he,decode_cons,ih,decode_cons]
      exact swap_middle _ _ _ (entry_ordered cap sigma B b) (entry_ordered cap rho A a)
        (decode_tags_ordered cap rest)

private theorem decode_merge (cap : Nat) (left right : CollectedPositiveTags) :
    decodeMultivariateCollectedTags cap (collectedTagsMerge left right)=
      decodeMultivariateCollectedTags cap left ⊞ decodeMultivariateCollectedTags cap right := by
  induction left using old_tags_induction with
  | nil => exact (MultivariateDictionary.structural_algebra.2.2.2.1 _).symm
  | cons rho A a rest ih =>
    rw [collectedTagsMerge,decode_insert,ih,decode_cons]
    exact (MultivariateDictionary.structural_algebra.2.2.1 _ _ _ (decode_tags_ordered cap right)).symm

theorem decode_add (cap : Nat) (A B : CollectedPositiveNF) :
    decodeMultivariateCollected cap (collectedPositiveAdd A B)=
      decodeMultivariateCollected cap A ⊞ decodeMultivariateCollected cap B := by
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      simp only [collectedPositiveAdd,decodeMultivariateCollected,decode_merge]
      change C (c+d) ⊞ (decodeMultivariateCollectedTags cap tags ⊞ decodeMultivariateCollectedTags cap rest)=
        (C c ⊞ decodeMultivariateCollectedTags cap tags) ⊞ (C d ⊞ decodeMultivariateCollectedTags cap rest)
      symm
      calc
        (C c ⊞ decodeMultivariateCollectedTags cap tags) ⊞ (C d ⊞ decodeMultivariateCollectedTags cap rest)=
            C c ⊞ (decodeMultivariateCollectedTags cap tags ⊞ (C d ⊞ decodeMultivariateCollectedTags cap rest)) :=
          MultivariateDictionary.structural_algebra.2.2.1 _ _ _
            (MultivariateDictionary.structural_algebra.1 _ _ (decode_tags_ordered cap rest))
        _ = C c ⊞ (C d ⊞ (decodeMultivariateCollectedTags cap tags ⊞ decodeMultivariateCollectedTags cap rest)) :=
          congrArg (C c ⊞ ·) (swap_middle _ _ _ (decode_tags_ordered cap tags) (C_ordered d)
            (decode_tags_ordered cap rest))
        _ = (C c ⊞ C d) ⊞ (decodeMultivariateCollectedTags cap tags ⊞ decodeMultivariateCollectedTags cap rest) :=
          (MultivariateDictionary.structural_algebra.2.2.1 _ _ _
            (MultivariateDictionary.structural_algebra.1 _ _ (decode_tags_ordered cap rest))).symm
        _ = C (c+d) ⊞ (decodeMultivariateCollectedTags cap tags ⊞ decodeMultivariateCollectedTags cap rest) := rfl

end LogicLineages.OrdinalComparison.MultivariateDirectNormalize
