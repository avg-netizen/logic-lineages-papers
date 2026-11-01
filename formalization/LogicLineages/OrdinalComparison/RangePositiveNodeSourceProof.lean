module
public import LogicLineages.OrdinalComparison.RangePositiveNodeTargets
public import LogicLineages.OrdinalComparison.OneVariableComparisonDomainsProof
public import LogicLineages.OrdinalComparison.SourceKernelCallsProof
public import LogicLineages.OrdinalComparison.SuffixKernelProof
public import LogicLineages.OrdinalComparison.LimitPairCertificateProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode

theorem word_expansive (w : List (ONote × Nat)) (t : Nat) : t≤(actualPrincipalWordRun w t).1 := by
  induction w generalizing t with
  | nil => exact le_rfl
  | cons p w ih =>
    exact (OneVariableComparison.kernel_expansive (Ordinal.omega0^p.1.repr) p.2 t).trans (ih _)

theorem open_growth : Targets.ActualOpenSourceUnconditionalGrowth := by
  intro E hv hopen x
  cases E with
  | positive E => exact OneVariableComparison.open_lower E hv hopen x
  | range w E =>
    exact (OneVariableComparison.open_lower E hv.2.2.1 hv.2.2.2 x).trans (word_expansive _ _)

private theorem last_split (word : List (NONote × Nat)) (hne : word≠[]) :
    ∃ (w : List (NONote × Nat)) (eta : NONote) (c : Nat),word=w++[(eta,c)] := by
  cases hr : word.reverse with
  | nil =>
    have h := congrArg List.reverse hr
    simp only [List.reverse_reverse,List.reverse_nil] at h
    exact (hne h).elim
  | cons p w =>
    rcases p with ⟨eta,c⟩
    refine ⟨w.reverse,eta,c,?_⟩
    have h := congrArg List.reverse hr
    simpa only [List.reverse_reverse,List.reverse_cons] using h

private theorem genuine_append (v w : List (ONote × Nat)) (t : Nat) :
    actualPrincipalWordGenuine (v++w) t ↔
      actualPrincipalWordGenuine v t ∧ actualPrincipalWordGenuine w (actualPrincipalWordRun v t).1 := by
  induction v generalizing t with
  | nil => simp [actualPrincipalWordGenuine,actualPrincipalWordRun]
  | cons p v ih =>
    rcases p with ⟨e,c⟩
    simp [actualPrincipalWordGenuine,actualPrincipalWordRun,ih,and_assoc]

theorem range_image : Targets.ActualGenuineRangeSourceImage := by
  intro word E hv x hd
  obtain ⟨w,eta,c,hw⟩ := last_split word hv.1
  subst word
  have hEta : 0<eta.1.repr := hv.2.1 (eta,c) (List.mem_append_right _ (List.mem_singleton_self _))
  have hlarge : Ordinal.omega0^eta.1.repr<epsilonZero := by
    rw [←(LimitPairCertificate.principal_source.2 eta).1]
    exact normalRepresentationSound _
  have hraw : comparisonRawWord (w++[(eta,c)])=comparisonRawWord w++[(eta.1,c)] := by
    simp [comparisonRawWord]
  change actualPrincipalWordGenuine (comparisonRawWord (w++[(eta,c)])) (actualFixedLimitProfileEval E x) at hd
  rw [hraw] at hd
  have hdom := ((genuine_append _ _ _).mp hd).2.1
  rw [SourceKernelCalls.shape_semantics.2.2 w eta c E x]
  have hi : actualOneVariableComparisonValue (comparisonLiteralInner w E) x=
      (actualPrincipalWordRun (comparisonRawWord w) (actualFixedLimitProfileEval E x)).1 := by
    cases w <;> rfl
  rw [hi]
  exact (actualSuffixKernelTrace eta.1.repr hEta hlarge c _ hdom).2.2.2.2.2

end LogicLineages.OrdinalComparison.RangePositiveNode
