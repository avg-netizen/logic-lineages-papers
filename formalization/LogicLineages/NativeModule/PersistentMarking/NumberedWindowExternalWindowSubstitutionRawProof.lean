module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalSubstitutionBottomProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalRawSubstitutionRootChecks
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalBindingNaturalityChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalWindowSubstitutionRawProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowExternalWindowSubstitutionTargets NumberedWindowPreservationGuardProof
open NumberedWindowExternalRawSubstitutionRootChecks NumberedWindowExternalBindingNaturalityChecks
open NumberedWindowExternalRawSubstitutionSelectProof (mappedCopies)
open NumberedWindowPreservationBoundProof (Compatible push)
open NumberedWindowPreservationSubstitutionProof (term)
open NumberedWindowNumberedDomainProof (ArgsGuard parts)
open NumberedWindowApplicationDomainProof (annotation)

def TermClaim (S : Spine.Signature) (K : List Ty) (q r : NTerm) : Prop :=
  ∀ values d C D, Compatible S K values d C D → InWindow S K C q.type q →
    RawStep S K (substitute values d q) (substitute values d r) ∨
      (substitute values d q = substitute values d r ∧ HasBottomValue values)

private def ArgsClaim (S : Spine.Signature) (K : List Ty) (qs rs : NArgs) : Prop :=
  ∀ values d C D, Compatible S K values d C D → ExtrasTyped C qs → ArgsGuard S K qs →
    RawArgsStep S K (substituteArgs values d qs) (substituteArgs values d rs) ∨
      (substituteArgs values d qs = substituteArgs values d rs ∧ HasBottomValue values)

theorem skeleton {S K q r} (hk : DecisionSourceUniverse.Closed K)
    (h : RawStep S K q r) : TermClaim S K q r := by
  induction h using RawStep.rec (motive_2 := fun qs rs _ => ArgsClaim S K qs rs) with
  | mark => intro _ _ _ _ _ _; exact .inl .mark
  | lower => intro _ _ _ _ _ _; exact .inl .lower
  | select hGet hType hApply =>
    intro values d C D hc hStart
    obtain ⟨hSelection, hArrow, hCall⟩ := exact_TypedSubstitutionSelect
      S K C D _ _ _ _ _ _ _ _ _ values d hk hc hStart hGet hType hApply
    exact .inl (.select hSelection hArrow hCall)
  | copy hPrec hTarget =>
    intro values d C D hc hStart
    simp only [substitute, mappedCopies]
    exact .inl (.copy hPrec hTarget)
  | stat hEq hTarget hReplace =>
    intro values d C D hc hStart
    exact .inl (.stat hEq hTarget (exact_SubstitutionPreservesPrimitiveReplacement values d _ _ hReplace))
  | fabs =>
    intro values d C D hc hStart
    simp only [substitute]
    rw [exact_SubstituteFreshBody values d]
    exact .inl .fabs
  | beta =>
    intro values d C D hc hStart
    simp only [substitute]
    rw [exact_SubstituteBeta values d]
    exact .inl .beta
  | bottom hn =>
    rename_i before
    intro values d C D hc hStart
    have hImageType := annotation (term S K hk values d C D _ _ hStart hc).1
    by_cases he : substitute values d before = .bottom before.type
    · exact .inr ⟨he, NumberedWindowExternalSubstitutionBottomProof.imageBottom values d before _ hn he⟩
    · have hRaw : RawStep S K (substitute values d before) (.bottom (substitute values d before).type) :=
        .bottom (by rwa [hImageType])
      rw [hImageType] at hRaw
      exact .inl hRaw
  | lam _ ih =>
    intro values d C D hc hStart
    rcases ih values (d + 1) _ _ (push hk hc) (lamBody hStart) with hStep | ⟨hEq, hBottom⟩
    · exact .inl (.lam hStep)
    · exact .inr ⟨by simp only [substitute, hEq], hBottom⟩
  | ordinaryBase _ ih =>
    intro values d C D hc hStart
    obtain ⟨hTyped, _, hGuard⟩ := ordinaryParts hStart
    rcases ih values d C D hc (toExtras hTyped) hGuard with hStep | ⟨hEq, hBottom⟩
    · exact .inl (.ordinaryBase hStep)
    · exact .inr ⟨by simp only [substitute, hEq], hBottom⟩
  | numberedBase _ ih =>
    intro values d C D hc hStart
    obtain ⟨hTyped, _, _, hGuard, _⟩ := parts hStart
    rcases ih values d C D hc (toExtras hTyped) hGuard with hStep | ⟨hEq, hBottom⟩
    · exact .inl (.numberedBase hStep)
    · exact .inr ⟨by simp only [substitute, hEq], hBottom⟩
  | numberedExtra _ ih =>
    intro values d C D hc hStart
    obtain ⟨_, hTyped, _, _, hGuard⟩ := parts hStart
    rcases ih values d C D hc hTyped hGuard with hStep | ⟨hEq, hBottom⟩
    · exact .inl (.numberedExtra hStep)
    · exact .inr ⟨by simp only [substitute, hEq], hBottom⟩
  | auxFunction _ ih =>
    intro values d C D hc hStart
    rcases ih values d C D hc (annotated (appParts hStart).1) with hStep | ⟨hEq, hBottom⟩
    · exact .inl (.auxFunction hStep)
    · exact .inr ⟨by simp only [substitute, hEq], hBottom⟩
  | first _ ih =>
    intro values d C D hc hTyped hGuard
    cases hTyped with
    | cons hHead _ =>
      rcases ih values d C D hc (annotated ⟨hHead, (consParts hGuard).1⟩) with hStep | ⟨hEq, hBottom⟩
      · exact .inl (.first hStep)
      · exact .inr ⟨by simp only [substituteArgs, hEq], hBottom⟩
  | later _ ih =>
    intro values d C D hc hTyped hGuard
    cases hTyped with
    | cons _ hTail =>
      rcases ih values d C D hc hTail (consParts hGuard).2 with hStep | ⟨hEq, hBottom⟩
      · exact .inl (.later hStep)
      · exact .inr ⟨by simp only [substituteArgs, hEq], hBottom⟩

end LogicLineages.PersistentMarking.NumberedWindowExternalWindowSubstitutionRawProof
