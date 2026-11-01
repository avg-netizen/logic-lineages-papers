module
public import LogicLineages.OrdinalComparison.RangePositiveNodeTargets
public import LogicLineages.OrdinalComparison.ComparisonNodeTailProof
public import LogicLineages.OrdinalComparison.ComparisonQueryProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionImageProof
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.RangePositiveNode

abbrev RootOrientations (q : ComparisonQuery) (w : List (NONote × Nat))
    (A P : FixedLimitPositiveExpr) : Prop :=
  q.1=(oneVariableComparisonEncode (.range w A),oneVariableComparisonEncode (.positive P)) ∨
  q.1=(oneVariableComparisonEncode (.positive P),oneVariableComparisonEncode (.range w A))

private theorem child_source (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range w A)) (hP : fixedLimitProfileBelow epsilonZero P)
    (a : NONote × FixedLimitPositiveExpr) (ha : a∈comparisonDisplayedSourceHeads P) :
    (oneVariableComparisonEncode (.range w A),oneVariableComparisonEncode (comparisonSourcePeakWord a.1 a.2))∈
      encodedComparisonChildren (oneVariableComparisonEncode (.range w A)) (oneVariableComparisonEncode (.positive P)) ∧
    (oneVariableComparisonEncode (.range w A),oneVariableComparisonEncode (comparisonSourcePeakWord a.1 a.2))∈
      encodedComparisonChildren (oneVariableComparisonEncode (.positive P)) (oneVariableComparisonEncode (.range w A)) := by
  have hHead : (rawNoteEncode a.1.1,positiveExprEncode a.2)∈encodedDisplayedSourceHeads (positiveExprEncode P) := by
    rw [SourceDisplayedHeads.program.2 P]
    exact List.mem_map.mpr ⟨a,ha,rfl⟩
  have hMap : (oneVariableComparisonEncode (.range w A),encodedSourcePeakWord (rawNoteEncode a.1.1) (positiveExprEncode a.2))∈
      (encodedDisplayedSourceHeads (positiveExprEncode P)).map
        (fun p => (oneVariableComparisonEncode (.range w A),encodedSourcePeakWord p.1 p.2)) :=
    List.mem_map.mpr ⟨(rawNoteEncode a.1.1,positiveExprEncode a.2),hHead,rfl⟩
  have hGuardRP : ¬(encodedComparisonSourceDomain (oneVariableComparisonEncode (.range w A))≠1 ∨
      encodedComparisonSourceDomain (oneVariableComparisonEncode (.positive P))≠1) := by
    rw [ComparisonSourceDomain.correct (.range w A) hR,ComparisonSourceDomain.correct (.positive P) hP]
    simp
  have hGuardPR : ¬(encodedComparisonSourceDomain (oneVariableComparisonEncode (.positive P))≠1 ∨
      encodedComparisonSourceDomain (oneVariableComparisonEncode (.range w A))≠1) := by
    rw [ComparisonSourceDomain.correct (.range w A) hR,ComparisonSourceDomain.correct (.positive P) hP]
    simp
  have hmodR : oneVariableComparisonEncode (.range w A)%2=1 := by
    change (2*Nat.pair _ _+1)%2=1
    omega
  have hmodP : oneVariableComparisonEncode (.positive P)%2=0 := by
    change (2*positiveExprEncode P)%2=0
    omega
  have hdivP : oneVariableComparisonEncode (.positive P)/2=positiveExprEncode P := by
    change (2*positiveExprEncode P)/2=positiveExprEncode P
    omega
  rw [←SourcePeakWord.program.2 a.1 a.2]
  constructor
  · unfold encodedComparisonChildren
    rw [if_neg hGuardRP]
    simpa only [hmodR,hmodP,Nat.one_ne_zero,if_false,if_true,hdivP] using hMap
  · unfold encodedComparisonChildren
    rw [if_neg hGuardPR]
    simpa only [hmodR,hmodP,Nat.one_ne_zero,if_false,if_true,hdivP] using hMap

theorem child_record (q : ComparisonQuery) (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range w A)) (hP : fixedLimitProfileBelow epsilonZero P)
    (hq : RootOrientations q w A P) (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (a : NONote × FixedLimitPositiveExpr) (ha : a∈comparisonDisplayedSourceHeads P)
    (profiles : Nat × Nat) (hp : profiles∈encodedComparisonQueryRequests q) :
    ∃ result : ComparisonNodeResult,
      (((oneVariableComparisonEncode (.range w A),oneVariableComparisonEncode (comparisonSourcePeakWord a.1 a.2)),profiles),result)∈table ∧
      actualComparisonQueryCorrect ((oneVariableComparisonEncode (.range w A),
        oneVariableComparisonEncode (comparisonSourcePeakWord a.1 a.2)),profiles) result := by
  have hs := child_source w A P hR hP a ha
  apply hc
  apply (ComparisonQuery.child_projection _ _).mpr
  refine ⟨?_,hp⟩
  rcases hq with hq | hq
  · rw [hq]
    exact hs.1
  · rw [hq]
    exact hs.2

theorem raw_peak_order_stable (q : ComparisonQuery) (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range w A)) (hP : fixedLimitProfileBelow epsilonZero P)
    (hq : RootOrientations q w A P) (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (a : NONote × FixedLimitPositiveExpr) (ha : a∈comparisonDisplayedSourceHeads P)
    (x y : Nat) (hx : encodedComparisonTableTail table≤x) (hy : encodedComparisonTableTail table≤y) :
    (actualOneVariableComparisonValue (.range w A) x≤actualOneVariableComparisonValue (comparisonSourcePeakWord a.1 a.2) x ↔
      actualOneVariableComparisonValue (.range w A) y≤actualOneVariableComparisonValue (comparisonSourcePeakWord a.1 a.2) y) := by
  obtain ⟨result,hm,hcorrect⟩ := child_record q w A P hR hP hq table hc a ha (1,1) (ComparisonQuery.coverage.2 q).1
  have hv := SourceDisplayedHeads.validity P hP a ha
  have hs := (hcorrect (.range w A) (comparisonSourcePeakWord a.1 a.2) rfl rfl hR
    (SourcePeakWord.semantics a.1 hv.1 hv.2.1 a.2 hv.2.2.1 hv.2.2.2).1).1
  have hn := ComparisonNode.table_member_tail table _ result hm
  exact ComparisonNode.weak_order_stable _ _ result hs x y (hn.trans hx) (hn.trans hy)

theorem root_peak_order_stable (q : ComparisonQuery) (w : List (NONote × Nat)) (A P : FixedLimitPositiveExpr)
    (hR : oneVariableComparisonValid (.range w A)) (hP : fixedLimitProfileBelow epsilonZero P)
    (hq : RootOrientations q w A P) (table : ComparisonNodeTable) (hc : comparisonQueryTableCovers q table)
    (rho : NONote) (B : CollectedPositiveNF) (hm : (rho,B)∈collectedSourceRootTags (collectedPositiveNormalize P))
    (x y : Nat) (hx : encodedComparisonTableTail table≤x) (hy : encodedComparisonTableTail table≤y) :
    (actualOneVariableComparisonValue (.range w A) x≤actualCollectedTagPeak rho B x ↔
      actualOneVariableComparisonValue (.range w A) y≤actualCollectedTagPeak rho B y) := by
  obtain ⟨raw,hraw,hnorm⟩ := SourceDisplayedHeads.root_provenance P hP rho B hm
  have hv := SourceDisplayedHeads.validity P hP (rho,raw) hraw
  have hpeak : ∀ z : Nat,actualOneVariableComparisonValue (comparisonSourcePeakWord rho raw) z=actualCollectedTagPeak rho B z := by
    intro z
    simpa only [hnorm] using (SourcePeakWord.semantics rho hv.1 hv.2.1 raw hv.2.2.1 hv.2.2.2).2 z |>.2.1
  simpa only [hpeak x,hpeak y] using raw_peak_order_stable q w A P hR hP hq table hc (rho,raw) hraw x y hx hy

end LogicLineages.OrdinalComparison.RangePositiveNode
