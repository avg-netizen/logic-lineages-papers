module
public import LogicLineages.OrdinalComparison.ComparisonExpansionTargets
public import LogicLineages.OrdinalComparison.SourceCarrierClosureProof
public import LogicLineages.OrdinalComparison.SourcePeakCallsProof
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonExpansion

/-- Abbreviation of the frozen full image theorem's EXACT conclusion. -/
abbrev ActualChildImage (budget : Nat) (E F : OneVariableComparisonExpr) (p : Nat × Nat) : Prop :=
  ∃ G H : OneVariableComparisonExpr,
    oneVariableComparisonEncode G=p.1 ∧ oneVariableComparisonEncode H=p.2 ∧
    oneVariableComparisonValid G ∧ oneVariableComparisonValid H ∧
    comparisonSourceBounded budget G ∧ comparisonSourceBounded budget H ∧
    Relation.TransGen (comparisonLiteralPairStep budget) (G,H) (E,F)

private theorem union_peak (budget : Nat) (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (hEB : comparisonSourceBounded budget (.positive E)) (hFB : comparisonSourceBounded budget (.positive F))
    (a : NONote × FixedLimitPositiveExpr) (ha : a∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F) :
    oneVariableComparisonValid (comparisonSourcePeakWord a.1 a.2) ∧
      comparisonSourceBounded budget (comparisonSourcePeakWord a.1 a.2) := by
  rcases List.mem_append.mp ha with ha | ha
  · have hv := SourceDisplayedHeads.validity E hE a ha
    exact ⟨(SourcePeakWord.semantics a.1 hv.1 hv.2.1 a.2 hv.2.2.1 hv.2.2.2).1,
      SourceCarrierClosure.peak budget E hEB a ha⟩
  · have hv := SourceDisplayedHeads.validity F hF a ha
    exact ⟨(SourcePeakWord.semantics a.1 hv.1 hv.2.1 a.2 hv.2.2.1 hv.2.2.2).1,
      SourceCarrierClosure.peak budget F hFB a ha⟩

theorem positive_image (budget : Nat) (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (hEB : comparisonSourceBounded budget (.positive E)) (hFB : comparisonSourceBounded budget (.positive F))
    (p : Nat × Nat) (hp : p∈encodedComparisonPositiveChildren (positiveExprEncode E) (positiveExprEncode F)) :
    ActualChildImage budget (.positive E) (.positive F) p := by
  have hH : encodedDisplayedSourceHeads (positiveExprEncode E)++encodedDisplayedSourceHeads (positiveExprEncode F)=
      (comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F).map
        (fun a => (rawNoteEncode a.1.1,positiveExprEncode a.2)) := by
    rw [SourceDisplayedHeads.program.2 E,SourceDisplayedHeads.program.2 F,List.map_append]
  dsimp only [encodedComparisonPositiveChildren] at hp
  rw [hH] at hp
  obtain ⟨aCode,haCode,hpA⟩ := List.mem_flatMap.mp hp
  obtain ⟨a,haRaw,haEq⟩ := List.mem_map.mp haCode
  subst aCode
  obtain ⟨bCode,hbCode,hpB⟩ := List.mem_flatMap.mp hpA
  obtain ⟨b,hbRaw,hbEq⟩ := List.mem_map.mp hbCode
  subst bCode
  by_cases heq : (rawNoteEncode a.1.1,positiveExprEncode a.2)=(rawNoteEncode b.1.1,positiveExprEncode b.2)
  · simp only [if_pos heq,List.not_mem_nil] at hpB
  · have hpval : p=(encodedSourcePeakWord (rawNoteEncode a.1.1) (positiveExprEncode a.2),
        encodedSourcePeakWord (rawNoteEncode b.1.1) (positiveExprEncode b.2)) := by
      simpa only [if_neg heq,List.mem_singleton] using hpB
    subst p
    have hne : a≠b := by intro h; apply heq; rw [h]
    have hA := union_peak budget E F hE hF hEB hFB a haRaw
    have hB := union_peak budget E F hE hF hEB hFB b hbRaw
    refine ⟨comparisonSourcePeakWord a.1 a.2,comparisonSourcePeakWord b.1 b.2,
      (SourcePeakWord.program.2 a.1 a.2).symm,(SourcePeakWord.program.2 b.1 b.2).symm,
      hA.1,hB.1,hA.2,hB.2,Relation.TransGen.single (Or.inl ?_)⟩
    have hlt := SourceDisplayedHeads.argument_drop.2 E F a b haRaw hbRaw hne
    change comparisonLiteralSourceHeadCount (comparisonSourcePeakWord a.1 a.2)+
      comparisonLiteralSourceHeadCount (comparisonSourcePeakWord b.1 b.2)<
        comparisonPositiveSourceHeadCount E+comparisonPositiveSourceHeadCount F
    simpa only [SourcePeakWord.shape.2.2] using hlt

theorem range_positive_image (budget : Nat) (Z : OneVariableComparisonExpr) (P : FixedLimitPositiveExpr)
    (hZ : oneVariableComparisonValid Z) (hP : fixedLimitProfileBelow epsilonZero P)
    (hZB : comparisonSourceBounded budget Z) (hPB : comparisonSourceBounded budget (.positive P))
    (p : Nat × Nat) (hp : p∈(encodedDisplayedSourceHeads (positiveExprEncode P)).map
      (fun a => (oneVariableComparisonEncode Z,encodedSourcePeakWord a.1 a.2))) :
    ActualChildImage budget Z (.positive P) p := by
  rw [SourceDisplayedHeads.program.2 P,List.map_map] at hp
  obtain ⟨a,ha,hp⟩ := List.mem_map.mp hp
  subst p
  have hv := SourceDisplayedHeads.validity P hP a ha
  have hA := (SourcePeakWord.semantics a.1 hv.1 hv.2.1 a.2 hv.2.2.1 hv.2.2.2).1
  refine ⟨Z,comparisonSourcePeakWord a.1 a.2,rfl,(SourcePeakWord.program.2 a.1 a.2).symm,
    hZ,hA,hZB,SourceCarrierClosure.peak budget P hPB a ha,Relation.TransGen.single (Or.inl ?_)⟩
  have hlt := SourceDisplayedHeads.argument_drop.1 P a ha
  change comparisonLiteralSourceHeadCount Z+comparisonLiteralSourceHeadCount (comparisonSourcePeakWord a.1 a.2)<
    comparisonLiteralSourceHeadCount Z+comparisonPositiveSourceHeadCount P
  rw [SourcePeakWord.shape.2.2]
  omega

theorem positive_range_image (budget : Nat) (P : FixedLimitPositiveExpr) (Z : OneVariableComparisonExpr)
    (hP : fixedLimitProfileBelow epsilonZero P) (hZ : oneVariableComparisonValid Z)
    (hPB : comparisonSourceBounded budget (.positive P)) (hZB : comparisonSourceBounded budget Z)
    (p : Nat × Nat) (hp : p∈(encodedDisplayedSourceHeads (positiveExprEncode P)).map
      (fun a => (oneVariableComparisonEncode Z,encodedSourcePeakWord a.1 a.2))) :
    ActualChildImage budget (.positive P) Z p := by
  rw [SourceDisplayedHeads.program.2 P,List.map_map] at hp
  obtain ⟨a,ha,hp⟩ := List.mem_map.mp hp
  subst p
  have hv := SourceDisplayedHeads.validity P hP a ha
  have hA := (SourcePeakWord.semantics a.1 hv.1 hv.2.1 a.2 hv.2.2.1 hv.2.2.2).1
  refine ⟨Z,comparisonSourcePeakWord a.1 a.2,rfl,(SourcePeakWord.program.2 a.1 a.2).symm,
    hZ,hA,hZB,SourceCarrierClosure.peak budget P hPB a ha,Relation.TransGen.single (Or.inl ?_)⟩
  have hlt := SourceDisplayedHeads.argument_drop.1 P a ha
  change comparisonLiteralSourceHeadCount Z+comparisonLiteralSourceHeadCount (comparisonSourcePeakWord a.1 a.2)<
    comparisonPositiveSourceHeadCount P+comparisonLiteralSourceHeadCount Z
  rw [SourcePeakWord.shape.2.2]
  omega

end LogicLineages.OrdinalComparison.ComparisonExpansion
