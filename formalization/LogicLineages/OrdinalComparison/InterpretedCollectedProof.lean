module
public import LogicLineages.OrdinalComparison.InterpretedCollectedTargets
public import LogicLineages.OrdinalComparison.CollectedNormalizeProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.InterpretedCollected

private theorem tags_induction {P : CollectedPositiveTags → Prop}
    (nil : P .nil) (cons : ∀ rho A a rest, P rest → P (.cons rho A a rest))
    (tags : CollectedPositiveTags) : P tags := by
  cases tags with
  | nil => exact nil
  | cons rho A a rest => exact cons rho A a rest (tags_induction nil cons rest)
termination_by tags

private theorem insert_value (H : NONote → Nat → Nat) (rho : NONote)
    (A : CollectedPositiveNF) (a : Nat) (tags : CollectedPositiveTags) (x : Nat) :
    interpretedCollectedTagsEval H (collectedTagInsert rho A a tags) x=
      a*H rho (interpretedCollectedEval H A x)+interpretedCollectedTagsEval H tags x := by
  induction tags using tags_induction with
  | nil =>
    by_cases ha : a=0 <;> simp [collectedTagInsert,ha,interpretedCollectedTagsEval]
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simp [collectedTagInsert,ha,interpretedCollectedTagsEval]
    by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
    · simp [collectedTagInsert,ha,hl,interpretedCollectedTagsEval]
    by_cases he : collectedTagKey rho A=collectedTagKey sigma B
    · rcases (collectedPositiveTagIdentity rho sigma A B).mp he with ⟨rfl,rfl⟩
      simp [collectedTagInsert,ha,interpretedCollectedTagsEval,Nat.add_mul,Nat.add_assoc]
    · simp only [collectedTagInsert,if_neg ha,if_neg hl,if_neg he,interpretedCollectedTagsEval,ih]
      omega

private theorem merge_value (H : NONote → Nat → Nat)
    (left right : CollectedPositiveTags) (x : Nat) :
    interpretedCollectedTagsEval H (collectedTagsMerge left right) x=
      interpretedCollectedTagsEval H left x+interpretedCollectedTagsEval H right x := by
  induction left using tags_induction with
  | nil => simp [collectedTagsMerge,interpretedCollectedTagsEval]
  | cons rho A a rest ih =>
    rw [collectedTagsMerge,insert_value,ih]
    simp only [interpretedCollectedTagsEval]
    omega

theorem addition : Targets.InterpretedCollectedAddition := by
  intro H A B x
  cases A with
  | mk c b tags =>
    cases B with
    | mk d e rest =>
      simp only [collectedPositiveAdd,interpretedCollectedEval,merge_value,Nat.add_mul]
      omega

private theorem closed_agreement (H : NONote → Nat → Nat) (E : FixedLimitPositiveExpr)
    (ha : PositiveClosedHeadAgreement H E) (hs : positiveExprHasInput E=false) (x : Nat) :
    interpretedPositiveEval H E x=actualFixedLimitProfileEval E x := by
  induction E with
  | constant c => rfl
  | input => cases hs
  | add E F ihE ihF =>
    have hab : positiveExprHasInput E=false ∧ positiveExprHasInput F=false := by
      simpa only [positiveExprHasInput,Bool.or_eq_false_iff] using hs
    exact congrArg₂ (·+·) (ihE ha.1 hab.1) (ihF ha.2 hab.2)
  | head rho E ih =>
    change H rho (interpretedPositiveEval H E x)=actualProfileHead rho (actualFixedLimitProfileEval E x)
    rw [ha.2 hs,ih ha.1 hs]

theorem normalization : Targets.InterpretedCollectedNormalization := by
  intro H E hv ha x
  induction E with
  | constant c => simp [collectedPositiveNormalize,interpretedCollectedEval,
      interpretedCollectedTagsEval,interpretedPositiveEval]
  | input => simp [collectedPositiveNormalize,interpretedCollectedEval,
      interpretedCollectedTagsEval,interpretedPositiveEval]
  | add E F ihE ihF =>
    rw [collectedPositiveNormalize,addition,ihE hv.1 ha.1,ihF hv.2 ha.2]
    rfl
  | head rho E ih =>
    by_cases hc : collectedPositiveSupport (collectedPositiveNormalize E)=false
    · have hinput : positiveExprHasInput E=false :=
        (collectedPositiveNormalizeSupport E hv.2.2).symm.trans hc
      simp only [collectedPositiveNormalize,if_pos hc,interpretedCollectedEval,
        interpretedCollectedTagsEval,Nat.zero_mul,Nat.add_zero]
      rw [encodedPositiveFoldSourceCorrect]
      change actualProfileHead rho (actualFixedLimitProfileEval E 0)=
        H rho (interpretedPositiveEval H E x)
      rw [ha.2 hinput,closed_agreement H E ha.1 hinput x,positiveInputAbsent E hinput x]
    · simp only [collectedPositiveNormalize,if_neg hc,interpretedCollectedEval,
        interpretedCollectedTagsEval,Nat.zero_mul,Nat.zero_add,Nat.one_mul,Nat.add_zero,
        interpretedPositiveEval,ih hv.2.2 ha.1]

private theorem insert_heads (P : NONote → Prop) (rho : NONote)
    (A : CollectedPositiveNF) (a : Nat) (tags : CollectedPositiveTags)
    (hρ : P rho) (hA : collectedHeadsSatisfy P A) (ht : collectedTagHeadsSatisfy P tags) :
    collectedTagHeadsSatisfy P (collectedTagInsert rho A a tags) := by
  induction tags using tags_induction with
  | nil =>
    by_cases ha : a=0
    · simp [collectedTagInsert,ha,collectedTagHeadsSatisfy]
    · rw [collectedTagInsert,if_neg ha]
      exact ⟨hρ,hA,True.intro⟩
  | cons sigma B b rest ih =>
    by_cases ha : a=0
    · simpa only [collectedTagInsert,if_pos ha] using ht
    by_cases hl : collectedTagKey rho A<collectedTagKey sigma B
    · rw [collectedTagInsert,if_neg ha,if_pos hl]
      exact ⟨hρ,hA,ht⟩
    by_cases he : collectedTagKey rho A=collectedTagKey sigma B
    · rw [collectedTagInsert,if_neg ha,if_neg hl,if_pos he]
      exact ht
    · rw [collectedTagInsert,if_neg ha,if_neg hl,if_neg he]
      exact ⟨ht.1,ht.2.1,ih ht.2.2⟩

private theorem merge_heads (P : NONote → Prop) (left right : CollectedPositiveTags)
    (hl : collectedTagHeadsSatisfy P left) (hr : collectedTagHeadsSatisfy P right) :
    collectedTagHeadsSatisfy P (collectedTagsMerge left right) := by
  induction left using tags_induction with
  | nil => exact hr
  | cons rho A a rest ih =>
    exact insert_heads P rho A a _ hl.1 hl.2.1 (ih hl.2.2)

theorem head_closure : Targets.CollectedNormalizationHeadClosure := by
  intro P E hp
  induction E with
  | constant c => trivial
  | input => trivial
  | add E F ihE ihF =>
    have hE := ihE hp.1
    have hF := ihF hp.2
    cases he : collectedPositiveNormalize E with
    | mk c b tags =>
      cases hf : collectedPositiveNormalize F with
      | mk d e rest =>
        simp only [collectedPositiveNormalize,he,hf,collectedPositiveAdd,collectedHeadsSatisfy]
        apply merge_heads P tags rest
        · simpa only [he,collectedHeadsSatisfy] using hE
        · simpa only [hf,collectedHeadsSatisfy] using hF
  | head rho E ih =>
    by_cases hc : collectedPositiveSupport (collectedPositiveNormalize E)=false
    · simp only [collectedPositiveNormalize,if_pos hc,collectedHeadsSatisfy,collectedTagHeadsSatisfy]
    · simp only [collectedPositiveNormalize,if_neg hc,collectedHeadsSatisfy,collectedTagHeadsSatisfy]
      exact ⟨hp.1,ih hp.2,True.intro⟩

end LogicLineages.OrdinalComparison.InterpretedCollected
