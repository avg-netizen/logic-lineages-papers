module
public import LogicLineages.OrdinalComparison.SourcePeakCallsTargets
public import LogicLineages.OrdinalComparison.SourcePeakWordProof
public import LogicLineages.OrdinalComparison.SourceDisplayedHeadsProof
public import LogicLineages.OrdinalComparison.SourceKernelMeasureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.SourcePeakCalls

theorem wellFounded : Targets.LiteralPairStepWellFounded := by
  intro budget
  exact InvImage.wf (fun p : OneVariableComparisonExpr × OneVariableComparisonExpr =>
    comparisonLiteralPairMeasure p.1 p.2) (SourceKernelMeasure.wellFounded budget)

private theorem union_valid (E F : FixedLimitPositiveExpr)
    (hE : fixedLimitProfileBelow epsilonZero E) (hF : fixedLimitProfileBelow epsilonZero F)
    (p : NONote × FixedLimitPositiveExpr)
    (hp : p∈comparisonDisplayedSourceHeads E++comparisonDisplayedSourceHeads F) :
    Order.IsSuccLimit p.1.1.repr ∧ p.1.1.repr<epsilonZero ∧
      fixedLimitProfileBelow epsilonZero p.2 ∧ positiveExprHasInput p.2=true := by
  rcases List.mem_append.mp hp with hp | hp
  · exact SourceDisplayedHeads.validity E hE p hp
  · exact SourceDisplayedHeads.validity F hF p hp

theorem positive_calls : Targets.ActualPositivePeakChildCalls := by
  intro budget E F hE hF
  dsimp only
  intro a ha b hb hkey
  obtain ⟨rawA,rawB,hA,hB,hnA,hnB,hlt⟩ :=
    (SourceDisplayedHeads.signed_argument_drop E F hE hF).2 a ha b hb hkey
  have hvA := union_valid E F hE hF (a.1.1,rawA) hA
  have hvB := union_valid E F hE hF (b.1.1,rawB) hB
  refine ⟨rawA,rawB,hA,hB,hnA,hnB,
    (SourcePeakWord.semantics a.1.1 hvA.1 hvA.2.1 rawA hvA.2.2.1 hvA.2.2.2).1,
    (SourcePeakWord.semantics b.1.1 hvB.1 hvB.2.1 rawB hvB.2.2.1 hvB.2.2.2).1,?_⟩
  apply Or.inl
  change comparisonLiteralSourceHeadCount (comparisonSourcePeakWord a.1.1 rawA)+
    comparisonLiteralSourceHeadCount (comparisonSourcePeakWord b.1.1 rawB)<
      comparisonPositiveSourceHeadCount E+comparisonPositiveSourceHeadCount F
  simpa only [SourcePeakWord.shape.2.2] using hlt

theorem range_calls : Targets.ActualRangePositivePeakChildCalls := by
  intro budget w A P hP p hp
  have hv := SourceDisplayedHeads.validity P hP p hp
  refine ⟨(SourcePeakWord.semantics p.1 hv.1 hv.2.1 p.2 hv.2.2.1 hv.2.2.2).1,Or.inl ?_⟩
  have hlt := SourceDisplayedHeads.argument_drop.1 P p hp
  change comparisonPositiveSourceHeadCount A+
    comparisonLiteralSourceHeadCount (comparisonSourcePeakWord p.1 p.2)<
      comparisonPositiveSourceHeadCount A+comparisonPositiveSourceHeadCount P
  rw [SourcePeakWord.shape.2.2]
  omega

theorem full : Targets.FullActualSourcePeakChildCalls := ⟨wellFounded,positive_calls,range_calls⟩

end LogicLineages.OrdinalComparison.SourcePeakCalls
