module
public import LogicLineages.OrdinalComparison.MultivariateNormalGrammarProof
public import LogicLineages.OrdinalComparison.CollectedMergeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateNormalValidity

attribute [local irreducible] Phi actualCollapse encodedMultivariateClosedValue

private theorem shadow_merge (left right : MultivariateCollectedTags) :
    multivariateCollectedTagsShadow (multivariateCollectedTagsMerge left right)=
      collectedTagsMerge (multivariateCollectedTagsShadow left) (multivariateCollectedTagsShadow right) := by
  have hn := MultivariateNormalizeCode.addition.2 (.mk 0 [] left) (.mk 0 [] right)
  have ht := congrArg (fun n : Nat => n.unpair.2.unpair.2) hn
  simp only [encodedMultivariateCollectedAdd,multivariateCollectedCode,multivariateCoefficientCode,
    Nat.unpair_pair,multivariateCollectedAdd,multivariateCoefficientAdd] at ht
  have ho := encodedCollectedMergeCorrect (multivariateCollectedTagsShadow left)
    (multivariateCollectedTagsShadow right)
  rw [MultivariateNormalizeCode.shadow_tags_code left,MultivariateNormalizeCode.shadow_tags_code right] at ho
  apply collectedPositiveCodeInjective.2
  exact (MultivariateNormalizeCode.shadow_tags_code _).trans (ht.symm.trans ho)

private theorem shadow_add (A B : MultivariateCollectedNF)
    (hA : CollectedPositiveValid (multivariateCollectedShadow A))
    (hB : CollectedPositiveValid (multivariateCollectedShadow B)) :
    CollectedPositiveValid (multivariateCollectedShadow (multivariateCollectedAdd A B)) ∧
      multivariateCollectedSupport (multivariateCollectedAdd A B)=
        (multivariateCollectedSupport A || multivariateCollectedSupport B) := by
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      have hm := collectedTagsMergeCorrect (multivariateCollectedTagsShadow tags)
        (multivariateCollectedTagsShadow rest) hA hB
      have hs : multivariateCollectedTagsSupport (multivariateCollectedTagsMerge tags rest)=
          (multivariateCollectedTagsSupport tags || multivariateCollectedTagsSupport rest) := by
        rw [←shadow_tags_support,shadow_merge,hm.2.1,shadow_tags_support,shadow_tags_support]
      refine ⟨?_,?_⟩
      · simpa only [multivariateCollectedAdd,multivariateCollectedShadow,CollectedPositiveValid,
          shadow_merge] using hm.1
      · cases b <;> cases e <;>
          simp [multivariateCollectedSupport,multivariateCollectedAdd,multivariateCoefficientAdd,
            hs,Bool.or_assoc,Bool.or_comm,Bool.or_left_comm] <;> rfl

private theorem insert_fields (d : Nat) (rho : NONote) (A : MultivariateCollectedNF) (a : Nat)
    (tags : MultivariateCollectedTags) (hA : MultivariateVectorFields d A)
    (ht : MultivariateVectorTagsFields d tags) :
    MultivariateVectorTagsFields d (multivariateCollectedTagInsert rho A a tags) := by
  induction tags using MultivariateDictionary.tags_induction with
  | nil =>
    by_cases ha : a=0
    · simp [multivariateCollectedTagInsert,ha,MultivariateVectorTagsFields]
    · simpa only [multivariateCollectedTagInsert,if_neg ha,MultivariateVectorTagsFields,and_true] using hA
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simpa only [multivariateCollectedTagInsert,if_pos ha] using ht
    by_cases hl : multivariateCollectedTagKey rho A<multivariateCollectedTagKey sigma B
    · simpa only [multivariateCollectedTagInsert,if_neg ha,if_pos hl,
        MultivariateVectorTagsFields] using And.intro hA ht
    by_cases he : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B
    · simpa only [multivariateCollectedTagInsert,if_neg ha,if_neg hl,if_pos he,
        MultivariateVectorTagsFields] using ht
    · rw [multivariateCollectedTagInsert,if_neg ha,if_neg hl,if_neg he]
      exact ⟨ht.1,ih ht.2⟩

private theorem merge_fields (d : Nat) (left right : MultivariateCollectedTags)
    (hl : MultivariateVectorTagsFields d left) (hr : MultivariateVectorTagsFields d right) :
    MultivariateVectorTagsFields d (multivariateCollectedTagsMerge left right) := by
  induction left using MultivariateDictionary.tags_induction with
  | nil => exact hr
  | cons rho A a rest ih => exact insert_fields d rho A a _ hl.1 (ih hl.2)

private theorem add_fields (d : Nat) (A B : MultivariateCollectedNF)
    (hA : MultivariateVectorFields d A) (hB : MultivariateVectorFields d B) :
    MultivariateVectorFields d (multivariateCollectedAdd A B) := by
  cases A with
  | mk c b tags =>
    cases B with
    | mk e f rest =>
      refine ⟨?_,coefficient_validity.1 b f hA.2.1 hB.2.1,merge_fields d tags rest hA.2.2 hB.2.2⟩
      rw [coefficient_validity.2.2 b f]
      exact Nat.max_le.mpr ⟨hA.1,hB.1⟩

private theorem source_fields (d : Nat) (E : MultivariatePositiveExpr) :
    multivariatePositiveValid d E → MultivariateVectorFields d (multivariateCollectedNormalize E) := by
  induction E with
  | constant c => intro _; exact ⟨Nat.zero_le d,Or.inl rfl,True.intro⟩
  | input i =>
    intro hv
    have h := coefficient_validity.2.1 d i hv
    exact ⟨h.1,h.2,True.intro⟩
  | add E F ihE ihF => intro hv; exact add_fields d _ _ (ihE hv.1) (ihF hv.2)
  | head rho E ih =>
    intro hv
    by_cases hz : multivariatePositiveHasInput E=false
    · rw [multivariateCollectedNormalize,if_pos hz]
      exact ⟨Nat.zero_le d,Or.inl rfl,True.intro⟩
    · rw [multivariateCollectedNormalize,if_neg hz]
      exact ⟨Nat.zero_le d,Or.inl rfl,ih hv.2.2,True.intro⟩

private theorem source_shadow (d : Nat) (E : MultivariatePositiveExpr) :
    multivariatePositiveValid d E →
      CollectedPositiveValid (multivariateCollectedShadow (multivariateCollectedNormalize E)) ∧
        multivariateCollectedSupport (multivariateCollectedNormalize E)=multivariatePositiveHasInput E := by
  induction E with
  | constant c =>
    intro _
    simp [multivariateCollectedNormalize,multivariateCollectedShadow,CollectedPositiveValid,
      CollectedTagsValid,multivariateCollectedTagsShadow,multivariateCollectedSupport,
      multivariateCollectedTagsSupport,multivariatePositiveHasInput]
  | input i =>
    intro _
    simp [multivariateCollectedNormalize,multivariateCollectedShadow,CollectedPositiveValid,
      CollectedTagsValid,multivariateCollectedTagsShadow,multivariateCollectedSupport,
      multivariateCollectedTagsSupport,multivariatePositiveHasInput,multivariateVariableCoefficients]
  | add E F ihE ihF =>
    intro hv
    have he := ihE hv.1
    have hf := ihF hv.2
    have h := shadow_add _ _ he.1 hf.1
    refine ⟨h.1,?_⟩
    simpa only [multivariateCollectedNormalize,multivariatePositiveHasInput,he.2,hf.2] using h.2
  | head rho E ih =>
    intro hv
    by_cases hz : multivariatePositiveHasInput E=false
    · simp [multivariateCollectedNormalize,hz,multivariateCollectedShadow,CollectedPositiveValid,
        multivariateCollectedTagsShadow,CollectedTagsValid,multivariateCollectedSupport,
        multivariateCollectedTagsSupport,multivariatePositiveHasInput]
    · have he := ih hv.2.2
      have hs : collectedPositiveSupport (multivariateCollectedShadow (multivariateCollectedNormalize E))=true := by
        rw [shadow_support,he.2]
        exact Bool.eq_true_of_not_eq_false hz
      rw [multivariateCollectedNormalize,if_neg hz]
      refine ⟨⟨hv.1,hv.2.1,he.1,hs,Nat.zero_lt_one,True.intro,True.intro⟩,?_⟩
      simpa only [multivariateCollectedSupport,multivariateCollectedTagsSupport,
        show (([] : List Nat) != [])=false from rfl,Bool.false_or,Bool.or_false,
        multivariatePositiveHasInput] using he.2

theorem full_validity : Targets.FullMultivariateNormalFormValidity := by
  intro d E hv
  have h := source_shadow d E hv
  exact ⟨(grammar.2 d _).mpr ⟨h.1,source_fields d E hv⟩,h.2⟩

end LogicLineages.OrdinalComparison.MultivariateNormalValidity
