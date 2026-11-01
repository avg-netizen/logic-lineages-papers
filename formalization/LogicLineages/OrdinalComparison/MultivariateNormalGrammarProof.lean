module
public import LogicLineages.OrdinalComparison.MultivariateNormalValidityTargets
public import LogicLineages.OrdinalComparison.MultivariateAdditionProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateNormalValidity

theorem shadow_key (rho : NONote) (A : MultivariateCollectedNF) :
    collectedTagKey rho (multivariateCollectedShadow A)=multivariateCollectedTagKey rho A := by
  simp only [collectedTagKey,multivariateCollectedTagKey,MultivariateNormalizeCode.shadow_code]

theorem shadow_above (k : Nat) (tags : MultivariateCollectedTags) :
    collectedTagsKeysAbove k (multivariateCollectedTagsShadow tags) ↔
      multivariateDictionaryKeysAbove k tags := by
  induction tags using MultivariateDictionary.tags_induction with
  | nil => rfl
  | cons rho A a rest ih =>
    simp only [collectedTagsKeysAbove,multivariateCollectedTagsShadow,multivariateDictionaryKeysAbove,
      shadow_key,ih]

mutual
  theorem shadow_support (A : MultivariateCollectedNF) :
      collectedPositiveSupport (multivariateCollectedShadow A)=multivariateCollectedSupport A := by
    cases A with
    | mk c b tags =>
      cases b with
      | nil => simp [multivariateCollectedShadow,collectedPositiveSupport,multivariateCollectedSupport,
          multivariateCoefficientCode,shadow_tags_support tags]
      | cons x xs => simp [multivariateCollectedShadow,collectedPositiveSupport,multivariateCollectedSupport,
          multivariateCoefficientCode,shadow_tags_support tags]
  theorem shadow_tags_support (tags : MultivariateCollectedTags) :
      collectedTagsSupport (multivariateCollectedTagsShadow tags)=multivariateCollectedTagsSupport tags := by
    cases tags with
    | nil => rfl
    | cons rho A a rest => exact congrArg₂ Bool.or (shadow_support A) (shadow_tags_support rest)
end

mutual
  private theorem grammar_form (d : Nat) (A : MultivariateCollectedNF) :
      MultivariateCollectedValid d A ↔
        CollectedPositiveValid (multivariateCollectedShadow A) ∧ MultivariateVectorFields d A := by
    cases A with
    | mk c b tags =>
      simp only [MultivariateCollectedValid,multivariateCollectedShadow,CollectedPositiveValid,
        MultivariateVectorFields,grammar_tags d tags]
      tauto
  private theorem grammar_tags (d : Nat) (tags : MultivariateCollectedTags) :
      MultivariateCollectedTagsValid d tags ↔
        CollectedTagsValid (multivariateCollectedTagsShadow tags) ∧ MultivariateVectorTagsFields d tags := by
    cases tags with
    | nil => simp [MultivariateCollectedTagsValid,multivariateCollectedTagsShadow,
        CollectedTagsValid,MultivariateVectorTagsFields]
    | cons rho A a rest =>
      simp only [MultivariateCollectedTagsValid,multivariateCollectedTagsShadow,CollectedTagsValid,
        MultivariateVectorTagsFields,grammar_form d A,grammar_tags d rest,shadow_support,
        shadow_key,shadow_above]
      tauto
end

theorem grammar : Targets.MultivariateNormalStorageGrammar := ⟨shadow_support,grammar_form⟩

theorem vector_length (a b : List Nat) :
    (multivariateCoefficientAdd a b).length=max a.length b.length := by
  induction a generalizing b with
  | nil => simp [multivariateCoefficientAdd]
  | cons x xs ih =>
    cases b with
    | nil => simp [multivariateCoefficientAdd]
    | cons y ys => simp only [multivariateCoefficientAdd,List.length_cons,ih]; omega

theorem vector_getD (a b : List Nat) (i : Nat) :
    (multivariateCoefficientAdd a b).getD i 0=a.getD i 0+b.getD i 0 := by
  induction a generalizing b i with
  | nil => simp [multivariateCoefficientAdd]
  | cons x xs ih =>
    cases b with
    | nil => simp [multivariateCoefficientAdd]
    | cons y ys =>
      cases i with
      | zero => rfl
      | succ i => simpa only [multivariateCoefficientAdd,List.getD_cons_succ] using ih ys i

private theorem canonical_add (a b : List Nat) (ha : MultivariateCoefficientCanonical a)
    (hb : MultivariateCoefficientCanonical b) : MultivariateCoefficientCanonical (multivariateCoefficientAdd a b) := by
  rcases ha with rfl | ha
  · exact hb
  rcases hb with rfl | hb
  · have he : multivariateCoefficientAdd a []=a := by cases a <;> rfl
    rw [he]
    exact Or.inr ha
  · apply Or.inr
    rw [vector_length,vector_getD]
    by_cases hlen : a.length≤b.length
    · rw [Nat.max_eq_right hlen]
      omega
    · rw [Nat.max_eq_left (Nat.le_of_not_ge hlen)]
      omega

private theorem variable_fields (d i : Nat) (hi : i<d) :
    (multivariateVariableCoefficients i 1).length≤d ∧
      MultivariateCoefficientCanonical (multivariateVariableCoefficients i 1) := by
  simp only [multivariateVariableCoefficients,show ¬(1:Nat)=0 from by decide,if_false]
  refine ⟨?_,Or.inr ?_⟩
  · simp only [List.length_append,List.length_replicate,List.length_singleton]
    omega
  · have hg : (List.replicate i 0 ++ [1]).getD i 0=1 := by
      rw [List.getD_append_right _ _ _ _ (by simp)]
      simp
    simpa only [List.length_append,List.length_replicate,List.length_singleton,
      Nat.add_sub_cancel_right,hg] using Nat.zero_lt_one

theorem coefficient_validity : Targets.MultivariateCoefficientValidity :=
  ⟨canonical_add,variable_fields,vector_length⟩

end LogicLineages.OrdinalComparison.MultivariateNormalValidity
