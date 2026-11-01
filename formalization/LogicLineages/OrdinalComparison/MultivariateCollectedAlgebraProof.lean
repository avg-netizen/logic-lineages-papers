module
public import LogicLineages.OrdinalComparison.MultivariateCollectedTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.MultivariateCollected

private theorem coefficient_injective (xs : List Nat) :
    ∀ ys : List Nat, multivariateCoefficientCode xs=multivariateCoefficientCode ys → xs=ys := by
  induction xs with
  | nil =>
    intro ys h
    cases ys with
    | nil => rfl
    | cons y ys => simp only [multivariateCoefficientCode] at h; omega
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp only [multivariateCoefficientCode] at h; omega
    | cons y ys =>
      have hp : x=y ∧ multivariateCoefficientCode xs=multivariateCoefficientCode ys := by
        simpa only [multivariateCoefficientCode,Nat.add_right_cancel_iff,Nat.pair_eq_pair] using h
      exact congrArg₂ List.cons hp.1 (ih ys hp.2)

mutual
  private theorem form_injective (A : MultivariateCollectedNF) :
      ∀ B : MultivariateCollectedNF, multivariateCollectedCode A=multivariateCollectedCode B → A=B := by
    cases A with
    | mk c b tags =>
      intro B h
      cases B with
      | mk d e rest =>
        have hp : c=d ∧ multivariateCoefficientCode b=multivariateCoefficientCode e ∧
            multivariateCollectedTagsCode tags=multivariateCollectedTagsCode rest := by
          simpa only [multivariateCollectedCode,Nat.pair_eq_pair] using h
        have hb := coefficient_injective b e hp.2.1
        have ht := tags_injective tags rest hp.2.2
        cases hp.1
        cases hb
        cases ht
        rfl
  private theorem tags_injective (tags : MultivariateCollectedTags) :
      ∀ rest : MultivariateCollectedTags,
        multivariateCollectedTagsCode tags=multivariateCollectedTagsCode rest → tags=rest := by
    cases tags with
    | nil =>
      intro rest h
      cases rest with
      | nil => rfl
      | cons rho A a rest => simp only [multivariateCollectedTagsCode] at h; omega
    | cons rho A a tail =>
      intro rest h
      cases rest with
      | nil => simp only [multivariateCollectedTagsCode] at h; omega
      | cons sigma B b rest =>
        have hp : (rawNoteEncode rho.1=rawNoteEncode sigma.1 ∧
            multivariateCollectedCode A=multivariateCollectedCode B) ∧
            a=b ∧ multivariateCollectedTagsCode tail=multivariateCollectedTagsCode rest := by
          simpa only [multivariateCollectedTagsCode,Nat.add_right_cancel_iff,Nat.pair_eq_pair] using h
        have hr : rho=sigma := by
          apply Subtype.ext
          have hz := congrArg rawNoteDecode hp.1.1
          rw [rawNoteDecodeEncode rho.1,rawNoteDecodeEncode sigma.1] at hz
          exact hz
        have hA := form_injective A B hp.1.2
        have ht := tags_injective tail rest hp.2.2
        rcases hp.2.1 with rfl
        subst rho
        subst A
        subst tail
        rfl
end

theorem storage : Targets.MultivariateCollectedStorageInjective :=
  ⟨fun A B h => form_injective A B h,fun A B h => tags_injective A B h⟩

private theorem tag_identity (rho sigma : NONote) (A B : MultivariateCollectedNF)
    (h : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B) : rho=sigma ∧ A=B := by
  have hp := Nat.pair_eq_pair.mp h
  refine ⟨?_,storage.1 hp.2⟩
  apply Subtype.ext
  have hz := congrArg rawNoteDecode hp.1
  rw [rawNoteDecodeEncode rho.1,rawNoteDecodeEncode sigma.1] at hz
  exact hz

private theorem coefficient_add_value (a b : List Nat) (rho : Nat → Nat) :
    multivariateCoefficientValue (multivariateCoefficientAdd a b) rho=
      multivariateCoefficientValue a rho+multivariateCoefficientValue b rho := by
  induction a generalizing b rho with
  | nil => simp [multivariateCoefficientAdd,multivariateCoefficientValue]
  | cons x xs ih =>
    cases b with
    | nil => simp [multivariateCoefficientAdd,multivariateCoefficientValue]
    | cons y ys =>
      simp only [multivariateCoefficientAdd,multivariateCoefficientValue,ih,Nat.add_mul]
      omega

private theorem variable_value (i a : Nat) (rho : Nat → Nat) :
    multivariateCoefficientValue (multivariateVariableCoefficients i a) rho=a*rho i := by
  by_cases ha : a=0
  · simp [multivariateVariableCoefficients,ha,multivariateCoefficientValue]
  · simp only [multivariateVariableCoefficients,if_neg ha]
    induction i generalizing rho with
    | zero => simp [multivariateCoefficientValue]
    | succ i ih =>
      simpa only [List.replicate_succ,List.cons_append,multivariateCoefficientValue,
        Nat.zero_mul,Nat.zero_add] using ih (fun j => rho (j+1))

private theorem tags_induction {P : MultivariateCollectedTags → Prop}
    (nil : P .nil) (cons : ∀ rho A a rest, P rest → P (.cons rho A a rest))
    (tags : MultivariateCollectedTags) : P tags := by
  cases tags with
  | nil => exact nil
  | cons rho A a rest => exact cons rho A a rest (tags_induction nil cons rest)
termination_by tags

private theorem insert_value (rho : NONote) (A : MultivariateCollectedNF) (a : Nat)
    (tags : MultivariateCollectedTags) (v : Nat → Nat) :
    actualMultivariateCollectedTagsValue (multivariateCollectedTagInsert rho A a tags) v=
      a*actualProfileHead rho (actualMultivariateCollectedValue A v)+
        actualMultivariateCollectedTagsValue tags v := by
  induction tags using tags_induction with
  | nil =>
    by_cases ha : a=0 <;> simp [multivariateCollectedTagInsert,ha,actualMultivariateCollectedTagsValue]
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simp [multivariateCollectedTagInsert,ha,actualMultivariateCollectedTagsValue]
    by_cases hl : multivariateCollectedTagKey rho A<multivariateCollectedTagKey sigma B
    · simp [multivariateCollectedTagInsert,ha,hl,actualMultivariateCollectedTagsValue]
    by_cases he : multivariateCollectedTagKey rho A=multivariateCollectedTagKey sigma B
    · rcases tag_identity rho sigma A B he with ⟨rfl,rfl⟩
      simp [multivariateCollectedTagInsert,ha,hl,actualMultivariateCollectedTagsValue,Nat.add_mul,Nat.add_assoc]
    · simp only [multivariateCollectedTagInsert,if_neg ha,if_neg hl,if_neg he,
        actualMultivariateCollectedTagsValue,ih]
      omega

private theorem merge_value (left right : MultivariateCollectedTags) (v : Nat → Nat) :
    actualMultivariateCollectedTagsValue (multivariateCollectedTagsMerge left right) v=
      actualMultivariateCollectedTagsValue left v+actualMultivariateCollectedTagsValue right v := by
  induction left using tags_induction with
  | nil => simp [multivariateCollectedTagsMerge,actualMultivariateCollectedTagsValue]
  | cons rho A a rest ih =>
    rw [multivariateCollectedTagsMerge,insert_value,ih]
    simp only [actualMultivariateCollectedTagsValue]
    omega

theorem additive : Targets.MultivariateCollectedAdditiveSemantics := by
  refine ⟨?_,variable_value⟩
  intro A B rho
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      simp only [multivariateCollectedAdd,actualMultivariateCollectedValue,coefficient_add_value,merge_value]
      omega

end LogicLineages.OrdinalComparison.MultivariateCollected
