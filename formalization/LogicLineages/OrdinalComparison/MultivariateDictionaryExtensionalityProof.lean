module
public import LogicLineages.OrdinalComparison.MultivariateDictionaryInsertionProof
public import LogicLineages.OrdinalComparison.MultivariateCollectedAlgebraProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateDictionary

private theorem coefficient_below (tags : MultivariateCollectedTags) (j k : Nat)
    (ht : multivariateDictionaryKeysAbove j tags) (hk : k≤j) :
    multivariateDictionaryCoefficient k tags=0 := by
  induction tags using tags_induction with
  | nil => rfl
  | cons rho A a rest ih =>
    have hn : k≠multivariateCollectedTagKey rho A := Nat.ne_of_lt (hk.trans_lt ht.1)
    simp only [multivariateDictionaryCoefficient,if_neg hn,ih ht.2,Nat.zero_add]

private theorem coefficient_head (rho : NONote) (A : MultivariateCollectedNF) (a : Nat)
    (tags : MultivariateCollectedTags)
    (ht : MultivariateDictionaryOrdered (.cons rho A a tags)) :
    multivariateDictionaryCoefficient (multivariateCollectedTagKey rho A) (.cons rho A a tags)=a := by
  simp [multivariateDictionaryCoefficient,
    coefficient_below tags _ _ ht.2.1 (Nat.le_refl _),Nat.add_zero]

private theorem coefficient_less_head (rho : NONote) (A : MultivariateCollectedNF) (a k : Nat)
    (tags : MultivariateCollectedTags)
    (ht : MultivariateDictionaryOrdered (.cons rho A a tags))
    (hk : k<multivariateCollectedTagKey rho A) :
    multivariateDictionaryCoefficient k (.cons rho A a tags)=0 := by
  simp only [multivariateDictionaryCoefficient,if_neg (Nat.ne_of_lt hk),
    coefficient_below tags _ _ ht.2.1 hk.le,Nat.zero_add]

private theorem tag_identity (rho sigma : NONote) (A B : MultivariateCollectedNF)
    (he : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B) :
    rho=sigma ∧ A=B := by
  have hp := Nat.pair_eq_pair.mp he
  refine ⟨?_,MultivariateCollected.storage.1 hp.2⟩
  apply Subtype.ext
  have hz := congrArg rawNoteDecode hp.1
  rw [rawNoteDecodeEncode rho.1,rawNoteDecodeEncode sigma.1] at hz
  exact hz

theorem extensionality : Targets.MultivariateDictionaryCanonicalExtensionality := by
  intro left
  induction left using tags_induction with
  | nil =>
    intro right _ hr he
    cases right with
    | nil => rfl
    | cons rho A a rest =>
      have h := he (multivariateCollectedTagKey rho A)
      rw [coefficient_head rho A a rest hr] at h
      change 0=a at h
      have ha := hr.1
      omega
  | cons rho A a rest ih =>
    intro right hl hr he
    cases right with
    | nil =>
      have h := he (multivariateCollectedTagKey rho A)
      rw [coefficient_head rho A a rest hl] at h
      change a=0 at h
      have ha := hl.1
      omega
    | cons sigma B b tail =>
      by_cases hlt : multivariateCollectedTagKey rho A<multivariateCollectedTagKey sigma B
      · have h := he (multivariateCollectedTagKey rho A)
        rw [coefficient_head rho A a rest hl,coefficient_less_head sigma B b _ tail hr hlt] at h
        have ha := hl.1
        omega
      by_cases hgt : multivariateCollectedTagKey sigma B<multivariateCollectedTagKey rho A
      · have h := he (multivariateCollectedTagKey sigma B)
        rw [coefficient_less_head rho A a _ rest hl hgt,coefficient_head sigma B b tail hr] at h
        have hb := hr.1
        omega
      have hk : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B := by omega
      rcases tag_identity rho sigma A B hk with ⟨rfl,rfl⟩
      have hab : a=b := by
        have h := he (multivariateCollectedTagKey rho A)
        rwa [coefficient_head rho A a rest hl,coefficient_head rho A b tail hr] at h
      subst b
      have ht : rest=tail := ih tail hl.2.2 hr.2.2 (by
        intro k
        by_cases hk : k=multivariateCollectedTagKey rho A
        · subst k
          rw [coefficient_below rest _ _ hl.2.1 (Nat.le_refl _),
            coefficient_below tail _ _ hr.2.1 (Nat.le_refl _)]
        · have h := he k
          simpa only [multivariateDictionaryCoefficient,if_neg hk,Nat.zero_add] using h)
      exact congrArg (MultivariateCollectedTags.cons rho A a) ht

private theorem vector_add_comm (a b : List Nat) :
    multivariateCoefficientAdd a b=multivariateCoefficientAdd b a := by
  induction a generalizing b with
  | nil => cases b <;> rfl
  | cons a rest ih =>
    cases b with
    | nil => rfl
    | cons b tail => simp only [multivariateCoefficientAdd,Nat.add_comm a b,ih tail]

private theorem vector_add_assoc (a b c : List Nat) :
    multivariateCoefficientAdd (multivariateCoefficientAdd a b) c=
      multivariateCoefficientAdd a (multivariateCoefficientAdd b c) := by
  induction a generalizing b c with
  | nil => rfl
  | cons a rest ih =>
    cases b with
    | nil => rfl
    | cons b tail =>
      cases c with
      | nil => rfl
      | cons c last => simp only [multivariateCoefficientAdd,Nat.add_assoc,ih tail last]

private theorem merge_comm (A B : MultivariateCollectedTags)
    (hA : MultivariateDictionaryOrdered A) (hB : MultivariateDictionaryOrdered B) :
    multivariateCollectedTagsMerge A B=multivariateCollectedTagsMerge B A := by
  apply extensionality _ _ (canonical_insertion.2 _ _ hB) (canonical_insertion.2 _ _ hA)
  intro k
  rw [coefficients.2 k A B,coefficients.2 k B A,Nat.add_comm]

private theorem merge_assoc (A B C : MultivariateCollectedTags)
    (hC : MultivariateDictionaryOrdered C) :
    multivariateCollectedTagsMerge (multivariateCollectedTagsMerge A B) C=
      multivariateCollectedTagsMerge A (multivariateCollectedTagsMerge B C) := by
  apply extensionality _ _ (canonical_insertion.2 _ _ hC)
    (canonical_insertion.2 _ _ (canonical_insertion.2 _ _ hC))
  intro k
  rw [coefficients.2 k _ C,coefficients.2 k A B,coefficients.2 k A _,coefficients.2 k B C,
    Nat.add_assoc]

private theorem merge_right_zero (A : MultivariateCollectedTags)
    (hA : MultivariateDictionaryOrdered A) : multivariateCollectedTagsMerge A .nil=A := by
  apply extensionality _ _ (canonical_insertion.2 A .nil True.intro) hA
  intro k
  rw [coefficients.2,multivariateDictionaryCoefficient,Nat.add_zero]

theorem structural_algebra : Targets.MultivariateCollectedStructuralAlgebra := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro A B hB
    cases A with
    | mk c b tags =>
      cases B with
      | mk d e rest => exact canonical_insertion.2 tags rest hB
  · intro A B hA hB
    cases A with
    | mk c b tags =>
      cases B with
      | mk d e rest =>
        simp only [multivariateCollectedAdd,Nat.add_comm c d,vector_add_comm b e,merge_comm tags rest hA hB]
  · intro A B C hC
    cases A with
    | mk c b tags =>
      cases B with
      | mk d e rest =>
        cases C with
        | mk f g last =>
          simp only [multivariateCollectedAdd,Nat.add_assoc,vector_add_assoc,merge_assoc tags rest last hC]
  · intro A
    cases A with
    | mk c b tags => simp [multivariateCollectedAdd,multivariateCoefficientAdd,multivariateCollectedTagsMerge]
  · intro A hA
    cases A with
    | mk c b tags =>
      have hb : multivariateCoefficientAdd b []=b := by cases b <;> rfl
      simp only [multivariateCollectedAdd,Nat.add_zero,hb,merge_right_zero tags hA]

end LogicLineages.OrdinalComparison.MultivariateDictionary
