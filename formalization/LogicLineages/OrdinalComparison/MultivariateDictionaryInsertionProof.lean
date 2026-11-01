module
public import LogicLineages.OrdinalComparison.MultivariateDictionaryTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateDictionary

theorem tags_induction {P : MultivariateCollectedTags → Prop}
    (nil : P .nil) (cons : ∀ rho A a rest, P rest → P (.cons rho A a rest))
    (tags : MultivariateCollectedTags) : P tags := by
  cases tags with
  | nil => exact nil
  | cons rho A a rest => exact cons rho A a rest (tags_induction nil cons rest)
termination_by tags

private theorem above_mono (tags : MultivariateCollectedTags) {k j : Nat}
    (hkj : k≤j) (h : multivariateDictionaryKeysAbove j tags) : multivariateDictionaryKeysAbove k tags := by
  induction tags using tags_induction with
  | nil => trivial
  | cons rho A a rest ih => exact ⟨hkj.trans_lt h.1,ih h.2⟩

private theorem insert_above (rho : NONote) (A : MultivariateCollectedNF) (a k : Nat)
    (tags : MultivariateCollectedTags) (hk : k<multivariateCollectedTagKey rho A)
    (ht : multivariateDictionaryKeysAbove k tags) :
    multivariateDictionaryKeysAbove k (multivariateCollectedTagInsert rho A a tags) := by
  induction tags using tags_induction with
  | nil =>
    by_cases ha : a=0
    · simp [multivariateCollectedTagInsert,ha,multivariateDictionaryKeysAbove]
    · simp only [multivariateCollectedTagInsert,if_neg ha,multivariateDictionaryKeysAbove]
      exact ⟨hk,True.intro⟩
  | cons sigma B b rest ih =>
    simp only [multivariateCollectedTagInsert]
    split
    · exact ht
    split
    · exact ⟨hk,ht⟩
    split
    · exact ht
    · exact ⟨ht.1,ih ht.2⟩

private theorem insert_ordered (rho : NONote) (A : MultivariateCollectedNF) (a : Nat)
    (tags : MultivariateCollectedTags) (ht : MultivariateDictionaryOrdered tags) :
    MultivariateDictionaryOrdered (multivariateCollectedTagInsert rho A a tags) := by
  induction tags using tags_induction with
  | nil =>
    by_cases ha : a=0
    · simp [multivariateCollectedTagInsert,ha,MultivariateDictionaryOrdered]
    · simp only [multivariateCollectedTagInsert,if_neg ha,MultivariateDictionaryOrdered,
        multivariateDictionaryKeysAbove,and_true]
      exact Nat.pos_of_ne_zero ha
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simpa only [multivariateCollectedTagInsert,if_pos ha] using ht
    by_cases hl : multivariateCollectedTagKey rho A<multivariateCollectedTagKey sigma B
    · rw [multivariateCollectedTagInsert,if_neg ha,if_pos hl]
      exact ⟨Nat.pos_of_ne_zero ha,⟨hl,above_mono rest hl.le ht.2.1⟩,ht⟩
    by_cases he : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B
    · rw [multivariateCollectedTagInsert,if_neg ha,if_neg hl,if_pos he]
      exact ⟨by omega,ht.2.1,ht.2.2⟩
    · rw [multivariateCollectedTagInsert,if_neg ha,if_neg hl,if_neg he]
      exact ⟨ht.1,insert_above rho A a _ rest (by omega) ht.2.1,ih ht.2.2⟩

private theorem merge_ordered (left right : MultivariateCollectedTags)
    (hr : MultivariateDictionaryOrdered right) :
    MultivariateDictionaryOrdered (multivariateCollectedTagsMerge left right) := by
  induction left using tags_induction with
  | nil => exact hr
  | cons rho A a rest ih => exact insert_ordered rho A a _ ih

theorem canonical_insertion : Targets.MultivariateDictionaryCanonicalInsertion :=
  ⟨insert_ordered,merge_ordered⟩

private theorem insert_coefficient (k : Nat) (rho : NONote) (A : MultivariateCollectedNF)
    (a : Nat) (tags : MultivariateCollectedTags) :
    multivariateDictionaryCoefficient k (multivariateCollectedTagInsert rho A a tags)=
      (if k=multivariateCollectedTagKey rho A then a else 0)+multivariateDictionaryCoefficient k tags := by
  induction tags using tags_induction with
  | nil =>
    by_cases ha : a=0 <;> simp [multivariateCollectedTagInsert,ha,multivariateDictionaryCoefficient]
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simp [multivariateCollectedTagInsert,ha,multivariateDictionaryCoefficient]
    by_cases hl : multivariateCollectedTagKey rho A<multivariateCollectedTagKey sigma B
    · simp [multivariateCollectedTagInsert,ha,hl,multivariateDictionaryCoefficient,Nat.add_assoc]
    by_cases he : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B
    · rw [multivariateCollectedTagInsert,if_neg ha,if_neg hl,if_pos he]
      by_cases hk : k=multivariateCollectedTagKey sigma B
      · simp [multivariateDictionaryCoefficient,hk,he,Nat.add_assoc]
      · have hkA : k≠multivariateCollectedTagKey rho A := by rwa [he]
        simp [multivariateDictionaryCoefficient,hk,hkA]
    · simp only [multivariateCollectedTagInsert,if_neg ha,if_neg hl,if_neg he,
        multivariateDictionaryCoefficient,ih]
      omega

private theorem merge_coefficient (k : Nat) (left right : MultivariateCollectedTags) :
    multivariateDictionaryCoefficient k (multivariateCollectedTagsMerge left right)=
      multivariateDictionaryCoefficient k left+multivariateDictionaryCoefficient k right := by
  induction left using tags_induction with
  | nil => simp [multivariateCollectedTagsMerge,multivariateDictionaryCoefficient]
  | cons rho A a rest ih =>
    rw [multivariateCollectedTagsMerge,insert_coefficient,ih]
    simp only [multivariateDictionaryCoefficient]
    omega

theorem coefficients : Targets.MultivariateDictionaryCoefficients :=
  ⟨insert_coefficient,merge_coefficient⟩

end LogicLineages.OrdinalComparison.MultivariateDictionary
