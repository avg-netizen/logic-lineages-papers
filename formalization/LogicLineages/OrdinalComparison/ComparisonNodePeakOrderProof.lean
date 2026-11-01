module
public import LogicLineages.OrdinalComparison.ComparisonNodeTailProof
public import LogicLineages.OrdinalComparison.ComparisonQueryProof
public import LogicLineages.OrdinalComparison.ComparisonExpansionImageProof
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonNode

abbrev positive_query (E F : FixedLimitPositiveExpr) (leftProfile rightProfile : Nat) : ComparisonQuery :=
  ((oneVariableComparisonEncode (.positive E),oneVariableComparisonEncode (.positive F)),(leftProfile,rightProfile))

private def head_code (p : NONote × FixedLimitPositiveExpr) : Nat × Nat :=
  (rawNoteEncode p.1.1,positiveExprEncode p.2)

private theorem union_valid (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (a : NONote × FixedLimitPositiveExpr) (ha : a∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F) :
    Order.IsSuccLimit a.1.1.repr ∧ a.1.1.repr<epsilonZero ∧
      fixedLimitProfileBelow epsilonZero a.2 ∧ positiveExprHasInput a.2=true := by
  rcases List.mem_append.mp ha with ha | ha
  · exact SourceDisplayedHeads.validity E hE a ha
  · exact SourceDisplayedHeads.validity F hF a ha

private theorem head_code_peak_eq (a b : NONote × FixedLimitPositiveExpr) (heq : head_code a=head_code b) :
    comparisonSourcePeakWord a.1 a.2=comparisonSourcePeakWord b.1 b.2 := by
  apply ComparisonExpansion.source_injective
  rw [←SourcePeakWord.program.2 a.1 a.2,←SourcePeakWord.program.2 b.1 b.2]
  exact congrArg (fun p : Nat × Nat => encodedSourcePeakWord p.1 p.2) heq

private theorem positive_child_query (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (leftProfile rightProfile : Nat) (a b : NONote × FixedLimitPositiveExpr)
    (ha : a∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F)
    (hb : b∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F)
    (hne : head_code a≠head_code b) :
    ((oneVariableComparisonEncode (comparisonSourcePeakWord a.1 a.2),
      oneVariableComparisonEncode (comparisonSourcePeakWord b.1 b.2)),(1,1))∈
        encodedComparisonQueryChildren (positive_query E F leftProfile rightProfile) := by
  have hH : encodedDisplayedSourceHeads (positiveExprEncode E)++encodedDisplayedSourceHeads (positiveExprEncode F)=
      (comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F).map head_code := by
    rw [SourceDisplayedHeads.program.2 E,SourceDisplayedHeads.program.2 F,List.map_append]
    rfl
  have hsource : (encodedSourcePeakWord (head_code a).1 (head_code a).2,
      encodedSourcePeakWord (head_code b).1 (head_code b).2)∈
        encodedComparisonPositiveChildren (positiveExprEncode E) (positiveExprEncode F) := by
    unfold encodedComparisonPositiveChildren
    rw [hH]
    exact List.mem_flatMap.mpr ⟨head_code a,List.mem_map.mpr ⟨a,ha,rfl⟩,
      List.mem_flatMap.mpr ⟨head_code b,List.mem_map.mpr ⟨b,hb,rfl⟩,by simp only [if_neg hne,List.mem_singleton]⟩⟩
  have hGuard : ¬(encodedComparisonSourceDomain (oneVariableComparisonEncode (.positive E))≠1 ∨
      encodedComparisonSourceDomain (oneVariableComparisonEncode (.positive F))≠1) := by
    rw [ComparisonSourceDomain.correct (.positive E) hE,ComparisonSourceDomain.correct (.positive F) hF]
    simp
  have hmE : (2*positiveExprEncode E)%2=0 := by omega
  have hmF : (2*positiveExprEncode F)%2=0 := by omega
  have hdE : (2*positiveExprEncode E)/2=positiveExprEncode E := by omega
  have hdF : (2*positiveExprEncode F)/2=positiveExprEncode F := by omega
  apply (ComparisonQuery.child_projection _ _).mpr
  refine ⟨?_,(ComparisonQuery.coverage.2 _).1⟩
  rw [←SourcePeakWord.program.2 a.1 a.2,←SourcePeakWord.program.2 b.1 b.2]
  change _∈encodedComparisonChildren (oneVariableComparisonEncode (.positive E)) (oneVariableComparisonEncode (.positive F))
  unfold encodedComparisonChildren
  rw [if_neg hGuard]
  simp only [oneVariableComparisonEncode,hmE,hmF,if_true,hdE,hdF]
  exact hsource

theorem raw_peak_order_stable (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (leftProfile rightProfile : Nat) (table : ComparisonNodeTable)
    (hcover : comparisonQueryTableCovers (positive_query E F leftProfile rightProfile) table)
    (a b : NONote × FixedLimitPositiveExpr)
    (ha : a∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F)
    (hb : b∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F)
    (x y : Nat) (hx : encodedComparisonTableTail table≤x) (hy : encodedComparisonTableTail table≤y) :
    (actualOneVariableComparisonValue (comparisonSourcePeakWord a.1 a.2) x≤
      actualOneVariableComparisonValue (comparisonSourcePeakWord b.1 b.2) x ↔
      actualOneVariableComparisonValue (comparisonSourcePeakWord a.1 a.2) y≤
        actualOneVariableComparisonValue (comparisonSourcePeakWord b.1 b.2) y) := by
  by_cases heq : head_code a=head_code b
  · rw [head_code_peak_eq a b heq]
    simp
  · have hquery := positive_child_query E F hE hF leftProfile rightProfile a b ha hb heq
    obtain ⟨result,hm,hcorrect⟩ := hcover _ hquery
    have hvA := union_valid E F hE hF a ha
    have hvB := union_valid E F hE hF b hb
    have hs := (hcorrect (comparisonSourcePeakWord a.1 a.2) (comparisonSourcePeakWord b.1 b.2)
      rfl rfl (SourcePeakWord.semantics a.1 hvA.1 hvA.2.1 a.2 hvA.2.2.1 hvA.2.2.2).1
        (SourcePeakWord.semantics b.1 hvB.1 hvB.2.1 b.2 hvB.2.2.1 hvB.2.2.2).1).1
    have hn := table_member_tail table _ result hm
    exact weak_order_stable _ _ result hs x y (hn.trans hx) (hn.trans hy)

theorem row_peak_order_stable (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (leftProfile rightProfile : Nat) (table : ComparisonNodeTable)
    (hcover : comparisonQueryTableCovers (positive_query E F leftProfile rightProfile) table)
    (a b : (NONote × CollectedPositiveNF) × Int)
    (ha : a∈(signedCollectedNFRow (collectedPositiveNormalize E) (collectedPositiveNormalize F)).2.2)
    (hb : b∈(signedCollectedNFRow (collectedPositiveNormalize E) (collectedPositiveNormalize F)).2.2)
    (x y : Nat) (hx : encodedComparisonTableTail table≤x) (hy : encodedComparisonTableTail table≤y) :
    (actualCollectedTagPeak a.1.1 a.1.2 x≤actualCollectedTagPeak b.1.1 b.1.2 x ↔
      actualCollectedTagPeak a.1.1 a.1.2 y≤actualCollectedTagPeak b.1.1 b.1.2 y) := by
  obtain ⟨rawA,hA,hnA⟩ := (SourceDisplayedHeads.signed_argument_drop E F hE hF).1 a ha
  obtain ⟨rawB,hB,hnB⟩ := (SourceDisplayedHeads.signed_argument_drop E F hE hF).1 b hb
  have hvA := union_valid E F hE hF (a.1.1,rawA) hA
  have hvB := union_valid E F hE hF (b.1.1,rawB) hB
  have hPA : ∀ z : Nat,actualOneVariableComparisonValue (comparisonSourcePeakWord a.1.1 rawA) z=
      actualCollectedTagPeak a.1.1 a.1.2 z := by
    intro z
    simpa only [hnA] using (SourcePeakWord.semantics a.1.1 hvA.1 hvA.2.1 rawA hvA.2.2.1 hvA.2.2.2).2 z |>.2.1
  have hPB : ∀ z : Nat,actualOneVariableComparisonValue (comparisonSourcePeakWord b.1.1 rawB) z=
      actualCollectedTagPeak b.1.1 b.1.2 z := by
    intro z
    simpa only [hnB] using (SourcePeakWord.semantics b.1.1 hvB.1 hvB.2.1 rawB hvB.2.2.1 hvB.2.2.2).2 z |>.2.1
  have hs := raw_peak_order_stable E F hE hF leftProfile rightProfile table hcover
    (a.1.1,rawA) (b.1.1,rawB) hA hB x y hx hy
  simpa only [hPA x,hPA y,hPB x,hPB y] using hs

end LogicLineages.OrdinalComparison.ComparisonNode
