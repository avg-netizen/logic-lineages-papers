module
public import LogicLineages.OrdinalComparison.CollectedOneInputTargets
public import LogicLineages.OrdinalComparison.EncodedCollectedThresholdProof
public import LogicLineages.OrdinalComparison.CollectedReachableProof
public import LogicLineages.OrdinalComparison.CommonBandOrbitProof
public import LogicLineages.OrdinalComparison.LimitTailUniquenessProof

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem family_threshold_pos (forms : List CollectedPositiveNF) :
    1≤collectedFamilyThreshold forms := by
  induction forms with
  | nil => exact le_rfl
  | cons A forms ih => exact ih.trans (le_max_right _ _)

private theorem threshold_le_family (forms : List CollectedPositiveNF) (A : CollectedPositiveNF)
    (h : A∈forms) : collectedOneInputThreshold A≤collectedFamilyThreshold forms := by
  induction forms with
  | nil => simp at h
  | cons B forms ih =>
    rcases List.mem_cons.mp h with h | h
    · subst A; exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem family_tag_domain (forms : List CollectedPositiveNF)
    (hv : ∀ A∈forms, CollectedPositiveValid A) (rho : NONote) (A : CollectedPositiveNF)
    (hm : (rho,A)∈collectedFamilyTags forms) :
    Order.IsSuccLimit rho.1.repr ∧ rho.1.repr<epsilonZero ∧
    CollectedPositiveValid A ∧ collectedPositiveSupport A=true ∧
    collectedAtomThreshold rho A≤collectedFamilyThreshold forms := by
  rcases List.mem_flatMap.mp hm with ⟨F,hF,hmem⟩
  have hd := (collectedReachableTagDomain F (hv F hF)).2 rho A hmem
  exact ⟨hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,
    hd.2.2.2.2.trans (threshold_le_family forms F hF)⟩

private theorem family_input_class (forms : List CollectedPositiveNF)
    (hv : ∀ A∈forms, CollectedPositiveValid A) (rho : NONote) (A : CollectedPositiveNF)
    (hm : (rho,A)∈collectedFamilyTags forms) (x : Nat) (hx : collectedFamilyThreshold forms≤x) :
    CommonBandOrRoot x (actualOrdinalNorm (actualCollectedTagInput rho A x)) := by
  have hd := family_tag_domain forms hv rho A hm
  cases A with
  | mk c b tags =>
    exact (collectedAtomInputRegime rho c b tags hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 x
      (hd.2.2.2.2.trans hx)).2.2

theorem fullActualCollectedOneInput : Targets.FullActualCollectedOneInput := by
  refine ⟨encodedCollectedThresholdPrimitiveRecursive.2,?_⟩
  intro forms hv
  dsimp only
  rw [encodedCollectedFamilyThresholdCorrect forms]
  refine ⟨rfl,family_threshold_pos forms,?_⟩
  intro x hx
  constructor
  · intro rho c b tags hm
    have hd := family_tag_domain forms hv rho (.mk c b tags) hm
    have hr := collectedAtomInputRegime rho c b tags hd.1 hd.2.1 hd.2.2.1 hd.2.2.2.1 x
      (hd.2.2.2.2.trans hx)
    exact ⟨hr.1,hr.2.1⟩
  · intro rho sigma A B hA hB heq
    have hdA := family_tag_domain forms hv rho A hA
    have hdB := family_tag_domain forms hv sigma B hB
    have ha := (actualFiniteTailClosureNorm rho.1.repr hdA.2.1 (actualCollectedPositiveEval A x)).1
    have hb := (actualFiniteTailClosureNorm sigma.1.repr hdB.2.1 (actualCollectedPositiveEval B x)).1
    have hna : Ordinal.omega0≤actualCollectedTagInput rho A x :=
      (Ordinal.omega0_le_of_isSuccLimit hdA.1).trans le_self_add
    have hnb : Ordinal.omega0≤actualCollectedTagInput sigma B x :=
      (Ordinal.omega0_le_of_isSuccLimit hdB.1).trans le_self_add
    have he := actualCommonBandPeakInjectivity (actualCollectedTagInput rho A x)
      (actualCollectedTagInput sigma B x) x ha hb hna hnb
      (family_input_class forms hv rho A hA x hx)
      (family_input_class forms hv sigma B hB x hx) heq
    exact actualLimitTailUniqueness rho sigma (actualCollectedPositiveEval A x)
      (actualCollectedPositiveEval B x) hdA.1 hdB.1 he

end LogicLineages.OrdinalComparison
