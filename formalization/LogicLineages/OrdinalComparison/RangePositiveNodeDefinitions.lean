module
public import LogicLineages.OrdinalComparison.ComparisonNodeDefinitions
public import LogicLineages.OrdinalComparison.KernelProfileLeafDefinitions
public import LogicLineages.OrdinalComparison.RangeAffineProgramDefinitions
public import LogicLineages.OrdinalComparison.CollectedRangeBandDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

noncomputable def encodedRangePositiveLocalTail (source positive profile : Nat) : Nat :=
  let form := encodedCollectedNormalize positive
  let outer := encodedComparisonOuter source
  let principal := encodedComparisonPrincipalNote outer.1
  max (encodedOneVariableComparisonDomainBound source)
    (max (encodedCollectedRangeThreshold form)
      (max (encodedRangeAffineTail source form.unpair.2.unpair.1 form.unpair.1)
        (encodedAffineProfileCertificateTail principal profile outer.2 form.unpair.2.unpair.1 form.unpair.1)))

noncomputable def encodedRangePositiveQueryNode (q : ComparisonQuery) (table : ComparisonNodeTable) : ComparisonNodeResult :=
  let positiveLeft := q.1.1%2=0
  let source := if positiveLeft then q.1.2 else q.1.1
  let positive := if positiveLeft then q.1.1/2 else q.1.2/2
  let profile := if positiveLeft then q.2.2 else q.2.1
  let threshold := max (encodedComparisonTableTail table) (encodedRangePositiveLocalTail source positive profile)
  (encodedSourcePairSignAt q.1.1 q.1.2 threshold,threshold)

end LogicLineages.OrdinalComparison
