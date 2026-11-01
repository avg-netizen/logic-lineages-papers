module
public import LogicLineages.OrdinalComparison.MultivariateCoefficientProgramProof
public import LogicLineages.OrdinalComparison.EncodedCollectedMergeProof
public import LogicLineages.OrdinalComparison.MultivariateDictionaryInsertionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateNormalizeCode

mutual
  theorem shadow_code (A : MultivariateCollectedNF) :
      collectedPositiveEncode (multivariateCollectedShadow A)=multivariateCollectedCode A := by
    cases A with
    | mk c b tags =>
      simp only [multivariateCollectedShadow,collectedPositiveEncode,multivariateCollectedCode,
        shadow_tags_code tags]
  theorem shadow_tags_code (tags : MultivariateCollectedTags) :
      collectedTagsEncode (multivariateCollectedTagsShadow tags)=multivariateCollectedTagsCode tags := by
    cases tags with
    | nil => rfl
    | cons rho A a rest =>
      simp only [multivariateCollectedTagsShadow,collectedTagsEncode,multivariateCollectedTagsCode,
        shadow_code A,shadow_tags_code rest,Nat.add_comm 1]
end

private theorem shadow_key (rho : NONote) (A : MultivariateCollectedNF) :
    collectedTagKey rho (multivariateCollectedShadow A)=multivariateCollectedTagKey rho A := by
  simp only [collectedTagKey,multivariateCollectedTagKey,shadow_code]

private theorem shadow_insert (rho : NONote) (A : MultivariateCollectedNF) (a : Nat)
    (tags : MultivariateCollectedTags) :
    multivariateCollectedTagsShadow (multivariateCollectedTagInsert rho A a tags)=
      collectedTagInsert rho (multivariateCollectedShadow A) a (multivariateCollectedTagsShadow tags) := by
  induction tags using MultivariateDictionary.tags_induction with
  | nil =>
    by_cases ha : a=0 <;> simp [multivariateCollectedTagInsert,collectedTagInsert,
      multivariateCollectedTagsShadow,ha]
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simp [multivariateCollectedTagInsert,collectedTagInsert,multivariateCollectedTagsShadow,ha]
    by_cases hl : multivariateCollectedTagKey rho A<multivariateCollectedTagKey sigma B
    · simp [multivariateCollectedTagInsert,collectedTagInsert,multivariateCollectedTagsShadow,ha,shadow_key,hl]
    by_cases he : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B
    · simp [multivariateCollectedTagInsert,collectedTagInsert,multivariateCollectedTagsShadow,ha,shadow_key,hl,he]
    · simp [multivariateCollectedTagInsert,collectedTagInsert,multivariateCollectedTagsShadow,ha,shadow_key,hl,he,ih]

private theorem shadow_merge (left right : MultivariateCollectedTags) :
    multivariateCollectedTagsShadow (multivariateCollectedTagsMerge left right)=
      collectedTagsMerge (multivariateCollectedTagsShadow left) (multivariateCollectedTagsShadow right) := by
  induction left using MultivariateDictionary.tags_induction with
  | nil => rfl
  | cons rho A a rest ih =>
    simp only [multivariateCollectedTagsMerge,shadow_insert,ih,multivariateCollectedTagsShadow,
      collectedTagsMerge]

private theorem numeric_merge (left right : MultivariateCollectedTags) :
    encodedCollectedMerge (multivariateCollectedTagsCode left) (multivariateCollectedTagsCode right)=
      multivariateCollectedTagsCode (multivariateCollectedTagsMerge left right) := by
  have h := encodedCollectedMergeCorrect (multivariateCollectedTagsShadow left) (multivariateCollectedTagsShadow right)
  rw [shadow_tags_code left,shadow_tags_code right,←shadow_merge,shadow_tags_code] at h
  exact h

theorem addition : Targets.MultivariateCollectedAdditionProgram := by
  refine ⟨?_,?_⟩
  · have hl : Primrec (fun p : Nat × Nat => p.1.unpair) := Primrec.unpair.comp Primrec.fst
    have hr : Primrec (fun p : Nat × Nat => p.2.unpair) := Primrec.unpair.comp Primrec.snd
    have hlt : Primrec (fun p : Nat × Nat => p.1.unpair.2.unpair) :=
      Primrec.unpair.comp (Primrec.snd.comp hl)
    have hrt : Primrec (fun p : Nat × Nat => p.2.unpair.2.unpair) :=
      Primrec.unpair.comp (Primrec.snd.comp hr)
    exact Primrec₂.natPair.comp (Primrec.nat_add.comp (Primrec.fst.comp hl) (Primrec.fst.comp hr))
      (Primrec₂.natPair.comp (coefficients.1.comp (Primrec.fst.comp hlt) (Primrec.fst.comp hrt))
        (encodedCollectedMergePrimitiveRecursive.comp (Primrec.snd.comp hlt) (Primrec.snd.comp hrt)))
  · intro A B
    cases A with
    | mk c b tags =>
      cases B with
      | mk d e rest =>
        simp only [encodedMultivariateCollectedAdd,multivariateCollectedCode,Nat.unpair_pair,
          coefficients.2.2.1 b e,numeric_merge,multivariateCollectedAdd]

end LogicLineages.OrdinalComparison.MultivariateNormalizeCode
