module
public import LogicLineages.OrdinalComparison.RangeRangeNodeTargets
public import LogicLineages.OrdinalComparison.ComparisonNodeProgramProof
public import LogicLineages.OrdinalComparison.RangePositiveNodeSourceProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionKernelImageProof
public import LogicLineages.OrdinalComparison.KernelInputProgramProof
public import LogicLineages.OrdinalComparison.ProfileDirectProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangeRangeNode

theorem inner_open (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr)
    (h : oneVariableComparisonValid (.range (w++[(eta,c)]) E)) :
    oneVariableComparisonOpen (comparisonLiteralInner w E) := by
  cases w with
  | nil => exact h.2.2.2
  | cons p w => exact True.intro

theorem inner_growth (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr)
    (h : oneVariableComparisonValid (.range (w++[(eta,c)]) E)) (x : Nat) :
    x≤actualOneVariableComparisonValue (comparisonLiteralInner w E) x :=
  RangePositiveNode.open_growth _ (SourceKernelCalls.shape_semantics.2.1 w eta c E h) (inner_open w eta c E h) x

theorem outer_unique (w v : List (NONote × Nat)) (eta lower : NONote) (c d : Nat)
    (E F : FixedLimitPositiveExpr) (h : OneVariableComparisonExpr.range (w++[(eta,c)]) E=
      .range (v++[(lower,d)]) F) : eta=lower ∧ c=d := by
  have hc := congrArg (fun source => encodedComparisonOuter (oneVariableComparisonEncode source)) h
  rw [ComparisonExpansion.outer_source w eta c E,ComparisonExpansion.outer_source v lower d F] at hc
  have hEta : eta=lower := by
    apply Subtype.ext
    have hd := congrArg (fun p : Nat × Nat => rawNoteDecode p.1) hc
    simpa only [rawNoteDecodeEncode eta.1,rawNoteDecodeEncode lower.1] using hd
  exact ⟨hEta,congrArg (fun p : Nat × Nat => p.2) hc⟩

theorem gap_vacuous (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr)
    (h : ¬Order.IsSuccLimit eta.1.repr) (F : OneVariableComparisonExpr) (profile N : Nat) :
    comparisonBareLimitGap (.range (w++[(eta,c)]) E) F profile N := by
  intro v lower d A heq hl
  have he := (outer_unique w v eta lower c d E A heq).1
  subst lower
  exact (h hl).elim

theorem kernel_strict (eta : NONote) (hp : 0<eta.1.repr) (c t : Nat)
    (hd : c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t) :
    t<actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t := by
  have hEps : Ordinal.omega0^eta.1.repr<epsilonZero := by
    rw [←(LimitPairCertificate.principal_source.2 eta).1]
    exact normalRepresentationSound _
  have hcount := (actualSuffixKernelTrace eta.1.repr hp hEps c t hd).1
  obtain ⟨n,hn⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hcount)
  unfold actualSuffixKernel
  rw [hn,Function.iterate_succ_apply]
  exact (self_lt_Phi t).trans_le (iterate_self_le (fun k => (self_lt_Phi k).le) n (Phi t))

theorem kernel_below_head (eta : NONote) (hp : 0<eta.1.repr) (c t : Nat)
    (hd : c+actualOrdinalNorm (Ordinal.omega0^eta.1.repr)≤t) :
    actualSuffixKernel (Ordinal.omega0^eta.1.repr) c t≤actualProfileHead (comparisonPrincipalNote eta) t := by
  have hEps : Ordinal.omega0^eta.1.repr<epsilonZero := by
    rw [←(LimitPairCertificate.principal_source.2 eta).1]
    exact normalRepresentationSound _
  have h := actualSuffixKernelBelowFixedHead eta.1.repr hp hEps c t hd
  simpa only [actualProfileHead,(LimitPairCertificate.principal_source.2 eta).1] using h

theorem input_classifier_stable (eta c d t u a b : Nat)
    (h : comparisonNaturalSign t u=comparisonNaturalSign a b) :
    encodedPrincipalKernelInputCompare eta c d t u=encodedPrincipalKernelInputCompare eta c d a b := by
  have hl : t<u ↔ a<b := by
    rw [←(ComparisonNode.natural_sign t u).2.1,←(ComparisonNode.natural_sign a b).2.1,h]
  have hr : u<t ↔ b<a := by
    rw [←(ComparisonNode.natural_sign t u).2.2.2,←(ComparisonNode.natural_sign a b).2.2.2,h]
  unfold encodedPrincipalKernelInputCompare
  simp only [hl,hr]

theorem sign_data_stable (E F : OneVariableComparisonExpr) (result : ComparisonNodeResult)
    (h : comparisonEventualSignData E F result) (x y : Nat) (hx : result.2≤x) (hy : result.2≤y) :
    comparisonNaturalSign (actualOneVariableComparisonValue E x) (actualOneVariableComparisonValue F x)=
      comparisonNaturalSign (actualOneVariableComparisonValue E y) (actualOneVariableComparisonValue F y) := by
  have hl : actualOneVariableComparisonValue E x<actualOneVariableComparisonValue F x ↔
      actualOneVariableComparisonValue E y<actualOneVariableComparisonValue F y := by
    rw [←(h.2.2 x hx).2.2.1,←(h.2.2 y hy).2.2.1]
  have hr : actualOneVariableComparisonValue F x<actualOneVariableComparisonValue E x ↔
      actualOneVariableComparisonValue F y<actualOneVariableComparisonValue E y := by
    rw [←(h.2.2 x hx).2.2.2.2,←(h.2.2 y hy).2.2.2.2]
  unfold comparisonNaturalSign
  simp only [hl,hr]

end LogicLineages.OrdinalComparison.RangeRangeNode
