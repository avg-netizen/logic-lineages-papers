module
public import LogicLineages.OrdinalComparison.CollectedPositiveTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison

mutual
  private theorem collected_nf_inj (A : CollectedPositiveNF) :
      ∀ B : CollectedPositiveNF, collectedPositiveEncode A=collectedPositiveEncode B → A=B := by
    cases A with
    | mk c b tags =>
      intro B h
      cases B with
      | mk d e rest =>
        have hp : c=d ∧ b=e ∧ collectedTagsEncode tags=collectedTagsEncode rest := by
          simpa only [collectedPositiveEncode,Nat.pair_eq_pair] using h
        rcases hp with ⟨rfl,rfl,ht⟩
        exact congrArg (CollectedPositiveNF.mk c b) (collected_tags_inj tags rest ht)
  private theorem collected_tags_inj (tags : CollectedPositiveTags) :
      ∀ rest : CollectedPositiveTags, collectedTagsEncode tags=collectedTagsEncode rest → tags=rest := by
    cases tags with
    | nil =>
      intro rest h
      cases rest with
      | nil => rfl
      | cons rho A a rest =>
        simp only [collectedTagsEncode] at h
        omega
    | cons rho A a tail =>
      intro rest h
      cases rest with
      | nil => simp [collectedTagsEncode] at h
      | cons sigma B b rest =>
        have hp : (rawNoteEncode rho.1=rawNoteEncode sigma.1 ∧
            collectedPositiveEncode A=collectedPositiveEncode B) ∧
            a=b ∧ collectedTagsEncode tail=collectedTagsEncode rest := by
          simpa only [collectedTagsEncode,Nat.add_left_cancel_iff,Nat.pair_eq_pair] using h
        have hr : rho=sigma := by
          apply Subtype.ext
          have hh := congrArg rawNoteDecode hp.1.1
          rw [rawNoteDecodeEncode rho.1,rawNoteDecodeEncode sigma.1] at hh
          exact hh
        have hA := collected_nf_inj A B hp.1.2
        have ht := collected_tags_inj tail rest hp.2.2
        rcases hp.2.1 with rfl
        subst rho
        subst A
        subst tail
        rfl
end

theorem collectedPositiveCodeInjective : Targets.CollectedPositiveCodeInjective :=
  ⟨fun A B h => collected_nf_inj A B h, fun A B h => collected_tags_inj A B h⟩

theorem collectedPositiveTagIdentity : Targets.CollectedPositiveTagIdentity := by
  intro rho sigma A B
  constructor
  · intro h
    have hp : rawNoteEncode rho.1=rawNoteEncode sigma.1 ∧
        collectedPositiveEncode A=collectedPositiveEncode B := Nat.pair_eq_pair.mp h
    refine ⟨?_,collectedPositiveCodeInjective.1 hp.2⟩
    apply Subtype.ext
    have hh := congrArg rawNoteDecode hp.1
    rw [rawNoteDecodeEncode rho.1,rawNoteDecodeEncode sigma.1] at hh
    exact hh
  · rintro ⟨rfl,rfl⟩
    rfl

theorem collectedPositiveSupportExact : Targets.CollectedPositiveSupportExact := by
  intro c b tags hv
  cases tags with
  | nil => simp [collectedPositiveSupport,collectedTagsSupport]
  | cons rho A a rest =>
    have hA : collectedPositiveSupport A=true := hv.2.2.2.1
    simp [collectedPositiveSupport,collectedTagsSupport,hA]

theorem collectedPositiveClosedValue : Targets.CollectedPositiveClosedValue := by
  intro c b tags hv hs x
  rcases (collectedPositiveSupportExact c b tags hv).mp hs with ⟨rfl,rfl⟩
  simp [actualCollectedPositiveEval,actualCollectedTagsEval]

theorem collectedPositiveHeightZero : Targets.CollectedPositiveHeightZero := by
  intro c b tags
  cases tags with
  | nil => simp [collectedPositiveHeight,collectedTagsHeight]
  | cons rho A a rest => simp [collectedPositiveHeight,collectedTagsHeight]

end LogicLineages.OrdinalComparison
