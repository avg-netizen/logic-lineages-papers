module
public import LogicLineages.OrdinalComparison.ComparisonNodeDefinitions
public import LogicLineages.OrdinalComparison.KernelProfileLeafDefinitions
public import LogicLineages.OrdinalComparison.LimitPairCertificateDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison

def encodedRangeRangeKernelTails (eta c d : Nat) (profiles : List Nat) : List Nat :=
  [encodedPrincipalKernelMassModulus eta c d]++profiles.flatMap (fun P =>
    [encodedLimitPairCertificateTail eta P c d,encodedLimitPairCertificateTail eta P d c,
      encodedKernelProfileLeafTail (encodedComparisonPrincipalNote eta) P c,
      encodedKernelProfileLeafTail (encodedComparisonPrincipalNote eta) P d])

def encodedRangeRangeNormalization (source : Nat × Nat) : Nat × Nat × Nat :=
  let a := encodedComparisonOuter source.1
  let b := encodedComparisonOuter source.2
  let high := if rawComparisonCode a.1 b.1=2 then source.1 else source.2
  let low := if rawComparisonCode a.1 b.1=2 then source.2 else source.1
  let H := encodedComparisonOuter high
  let M := encodedComparisonOuter low
  encodedSuccessorNormalization (encodedComparisonRangePrefix high) H.1 M.1 H.2

def encodedRangeRangeLocalTails (q : ComparisonQuery) : List Nat :=
  let a := encodedComparisonOuter q.1.1
  let b := encodedComparisonOuter q.1.2
  let result := encodedRangeRangeNormalization q.1
  [encodedOneVariableComparisonDomainBound q.1.1,encodedOneVariableComparisonDomainBound q.1.2,
    result.2.2,encodedOneVariableComparisonDomainBound result.1,
    encodedOneVariableComparisonDomainBound (encodedComparisonStripOuter q.1.1),
    encodedOneVariableComparisonDomainBound (encodedComparisonStripOuter q.1.2),
    encodedOneVariableComparisonDomainBound (encodedComparisonStripOuter result.1)]++
      [a.1,b.1,result.2.1].flatMap (fun eta => encodedRangeRangeKernelTails eta a.2 b.2 [q.2.1,q.2.2,1])

def encodedRangeRangeLocalTail (q : ComparisonQuery) : Nat := (encodedRangeRangeLocalTails q).foldr max 1

noncomputable def encodedRangeRangeQueryNode (q : ComparisonQuery) (table : ComparisonNodeTable) : ComparisonNodeResult :=
  let threshold := max (encodedComparisonTableTail table) (encodedRangeRangeLocalTail q)
  (encodedSourcePairSignAt q.1.1 q.1.2 threshold,threshold)

end LogicLineages.OrdinalComparison
