module
public import LogicLineages.OrdinalComparison.RangePositiveNodeSignProof
public import LogicLineages.OrdinalComparison.KernelProfileLeafProof
public import LogicLineages.OrdinalComparison.ProfileCompositionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode

private theorem entry_direct (tags : CollectedPositiveTags) (rho : NONote) (B : CollectedPositiveNF) (a : Nat)
    (hm : (rho,B,a)∈collectedTagEntries tags) : (rho,B)∈collectedDirectTags tags := by
  cases tags with
  | nil => cases hm
  | cons sigma C c rest =>
    rcases List.mem_cons.mp hm with heq | hm
    · cases heq
      exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (entry_direct rest rho B a hm)
termination_by tags

private theorem limit_large (eta : NONote) (hl : Order.IsSuccLimit eta.1.repr) :
    Ordinal.omega0<Ordinal.omega0^eta.1.repr := by
  simpa only [Ordinal.opow_one] using
    ((Ordinal.opow_lt_opow_iff_right Ordinal.one_lt_omega0).mpr (Ordinal.one_lt_of_isSuccLimit hl))

private theorem omega_context_below (eta : NONote) (hl : Order.IsSuccLimit eta.1.repr) :
    fixedLimitProfileBelow (Ordinal.omega0^eta.1.repr) (.head profileOmegaNote .input) := by
  refine ⟨?_,?_,True.intro⟩
  · rw [actualOmegaProfileHead.1]
    exact Ordinal.isSuccLimit_omega0
  · rw [actualOmegaProfileHead.1]
    exact limit_large eta hl

theorem peak_requested_gap (q : ComparisonQuery) (w : List (NONote × Nat)) (eta : NONote) (mass : Nat)
    (A P : FixedLimitPositiveExpr) (hR : oneVariableComparisonValid (.range (w++[(eta,mass)]) A))
    (hP : fixedLimitProfileBelow epsilonZero P) (hq : RootOrientations q (w++[(eta,mass)]) A P)
    (hl : Order.IsSuccLimit eta.1.repr) (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (profile N : Nat) (hprofile : profile∈[q.2.1,q.2.2]) (hNT : encodedComparisonTableTail table≤N)
    (Q : FixedLimitPositiveExpr) (hQc : positiveExprEncode Q=profile)
    (hQ : fixedLimitProfileBelow (Ordinal.omega0^eta.1.repr) Q)
    (rho : NONote) (B : CollectedPositiveNF) (hm : (rho,B)∈collectedSourceRootTags (collectedPositiveNormalize P))
    (hPeakN : actualCollectedTagPeak rho B N<actualOneVariableComparisonValue (.range (w++[(eta,mass)]) A) N)
    (x : Nat) (hx : N≤x) :
    actualFixedLimitProfileEval (fixedProfileCompose Q (.head profileOmegaNote .input)) (actualCollectedTagPeak rho B x)<
      actualOneVariableComparisonValue (.range (w++[(eta,mass)]) A) x := by
  obtain ⟨raw,hraw,hnorm⟩ := SourceDisplayedHeads.root_provenance P hP rho B hm
  have hv := SourceDisplayedHeads.validity P hP (rho,raw) hraw
  have hPeakValid := (SourcePeakWord.semantics rho hv.1 hv.2.1 raw hv.2.2.1 hv.2.2.2).1
  have hPeak : ∀ z : Nat,actualOneVariableComparisonValue (comparisonSourcePeakWord rho raw) z=actualCollectedTagPeak rho B z := by
    intro z
    simpa only [hnorm] using (SourcePeakWord.semantics rho hv.1 hv.2.1 raw hv.2.2.1 hv.2.2.2).2 z |>.2.1
  have hctx : positiveExprEncode (.head profileOmegaNote .input)∈encodedComparisonQueryContexts q.1 := by
    simp [encodedComparisonQueryContexts]
  have hreq := ((ComparisonQuery.coverage.2 q).2.2 profile hprofile
    (positiveExprEncode (.head profileOmegaNote .input)) hctx).1
  have hcompCode : encodedProfileCompose profile (positiveExprEncode (.head profileOmegaNote .input))=
      positiveExprEncode (fixedProfileCompose Q (.head profileOmegaNote .input)) := by
    rw [←hQc]
    exact ProfileComposition.program.2 Q _
  rw [hcompCode] at hreq
  obtain ⟨result,hmTable,hcorrect⟩ := child_record q (w++[(eta,mass)]) A P hR hP hq table hc
    (rho,raw) hraw (positiveExprEncode (fixedProfileCompose Q (.head profileOmegaNote .input)),1) hreq
  have hn := ComparisonNode.table_member_tail table _ result hmTable
  have hData := hcorrect (.range (w++[(eta,mass)]) A) (comparisonSourcePeakWord rho raw) rfl rfl hR hPeakValid
  have hSig : result.1=2 := (hData.1.2.2 N (hn.trans hNT)).2.2.2.2.mpr (by rw [hPeak N]; exact hPeakN)
  have hGap := hData.2.1 hSig w eta mass A rfl hl (fixedProfileCompose Q (.head profileOmegaNote .input)) rfl
    (ProfileComposition.source _ Q _ hQ (omega_context_below eta hl)).1 x (hn.trans (hNT.trans hx))
  simpa only [hPeak x] using hGap

theorem requested_gap (q : ComparisonQuery) (word : List (NONote × Nat)) (A P : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range word A)) (hP : fixedLimitProfileBelow epsilonZero P)
    (hq : RootOrientations q word A P) (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (profile N : Nat) (hprofile : profile∈[q.2.1,q.2.2]) (hNT : encodedComparisonTableTail table≤N)
    (hNL : encodedRangePositiveLocalTail (oneVariableComparisonEncode (.range word A)) (positiveExprEncode P) profile≤N)
    (hWin : ∀ x : Nat,N≤x → actualFixedLimitProfileEval P x<actualOneVariableComparisonValue (.range word A) x) :
    comparisonBareLimitGap (.range word A) (.positive P) profile N := by
  intro w eta mass B hEq hl Q hQc hQ x hx
  injection hEq with hword hA
  subst word A
  cases hNF : collectedPositiveNormalize P with
  | mk c b tags =>
    cases tags with
    | nil =>
      have hInnerValid := SourceKernelCalls.shape_semantics.2.1 w eta mass B hR
      have hInnerOpen : oneVariableComparisonOpen (comparisonLiteralInner w B) := by
        cases w with
        | nil => exact hR.2.2.2
        | cons p w => exact True.intro
      have hGrowth := open_growth _ hInnerValid hInnerOpen x
      have hL := (LimitPairCertificate.principal_source.2 eta).1
      have hBelow : fixedLimitProfileBelow (comparisonPrincipalNote eta).1.repr Q := by
        rw [hL]
        exact hQ
      have hLarge : Ordinal.omega0<(comparisonPrincipalNote eta).1.repr := by
        rw [hL]
        exact limit_large eta hl
      have hCut : encodedAffineProfileCertificateTail (rawNoteEncode (comparisonPrincipalNote eta).1)
          (positiveExprEncode Q) mass b c≤x := by
        rw [hQc]
        exact (local_affine_profile_bound w B P hP eta mass profile c b .nil hNF).trans (hNL.trans hx)
      have hAff := (KernelProfileLeaf.affine_inputs_program.2 (comparisonPrincipalNote eta)
        ⟨eta.1.repr,hL⟩ hLarge Q hBelow mass b c x _ hCut hGrowth).2
      have hPvalue : actualFixedLimitProfileEval P x=b*x+c := by
        rw [←collectedPositiveNormalizeValue P hP x,hNF]
        simp [actualCollectedPositiveEval,actualCollectedTagsEval,Nat.add_comm]
      change actualFixedLimitProfileEval Q (actualFixedLimitProfileEval P x)<
        actualOneVariableComparisonValue (.range (w++[(eta,mass)]) B) x
      rw [hPvalue,SourceKernelCalls.shape_semantics.2.2 w eta mass B x]
      simpa only [hL] using hAff
    | cons sigma C d rest =>
      let tags : CollectedPositiveTags := .cons sigma C d rest
      have hTags : CollectedTagsValid tags := by
        have hv := collectedPositiveNormalizeValid P hP
        rw [hNF] at hv
        exact hv
      have hn : tags≠.nil := by
        change CollectedPositiveTags.cons sigma C d rest≠.nil
        intro h
        cases h
      have hRangeN : collectedRangeThreshold (.mk c b tags)≤N := by
        have h := (local_range_bound _ P hP profile).trans hNL
        simpa only [hNF,tags] using h
      have hRangeX := hRangeN.trans hx
      have hTwoX : 2≤x := by
        have hFour : 4≤x := (Nat.le_max_left _ _).trans hRangeX
        omega
      have hDomN : oneVariableComparisonDomainAt (.range (w++[(eta,mass)]) B) N :=
        ((OneVariableComparison.source_program.2.2 _ hR).2.2 N (by
          rw [←(OneVariableComparison.source_program.2.2 _ hR).1]
          exact (local_domain_bound _ _ profile).trans hNL)).1
      have hCellN := collectedRangeCellTests c b tags hTags hn N hRangeN _ (range_image _ B hR N hDomN)
      have hAllPeakN := hCellN.2.1.mp (show actualCollectedPositiveEval (.mk c b tags) N<
          actualOneVariableComparisonValue (.range (w++[(eta,mass)]) B) N from by
        change actualCollectedPositiveEval (.mk c b (.cons sigma C d rest)) N<_
        rw [←hNF,collectedPositiveNormalizeValue P hP N]
        exact hWin N le_rfl)
      obtain ⟨rho,D,a,hm,hmax⟩ := (collectedMaximumPeak tags hTags hn x hTwoX).2.2.1
      have hRoot : (rho,D)∈collectedSourceRootTags (collectedPositiveNormalize P) := by
        rw [hNF]
        exact entry_direct tags rho D a hm
      have hGap := peak_requested_gap q w eta mass B P hR hP hq hl table hc profile N hprofile hNT Q hQc hQ
        rho D hRoot (hAllPeakN rho D a hm) x hx
      rw [(ProfileComposition.source _ Q _ hQ (omega_context_below eta hl)).2 _] at hGap
      have hBand := collectedNonlinearRangeBand c b tags hTags hn x hRangeX
      obtain ⟨s,hY,hlo,hhi,hOmega⟩ := hBand
      have hUpper : actualFixedLimitProfileEval P x<actualProfileHead profileOmegaNote (actualCollectedTagPeak rho D x) := by
        rw [←collectedPositiveNormalizeValue P hP x,hNF]
        simpa only [hmax] using hOmega
      change actualFixedLimitProfileEval Q (actualFixedLimitProfileEval P x)<_
      exact (actualFixedLimitProfileMonotone _ Q hQ hUpper.le).trans_lt hGap

end LogicLineages.OrdinalComparison.RangePositiveNode
