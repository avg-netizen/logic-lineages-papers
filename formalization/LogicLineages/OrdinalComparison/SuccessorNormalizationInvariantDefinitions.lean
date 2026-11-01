module
public import LogicLineages.OrdinalComparison.SuccessorNormalizationTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison

/-- Full literal source invariant for the numeric trace. This is a predicate
to be PROVED for the actual bounded program, not a normalizer interface. -/
def SuccessorNormalizationSourceInvariant (w : List (NONote × Nat))
    (E : FixedLimitPositiveExpr) (eta lower : NONote) (c k : Nat) (s : SuccessorNormalizationState) : Prop :=
  ∃ (added : List (NONote × Nat)) (last : NONote),
    s.1=oneVariableComparisonEncode (.range (w++added) E) ∧ s.2.1=rawNoteEncode last.1 ∧
    oneVariableComparisonValid (.range ((w++added)++[(last,c)]) E) ∧
    lower.1.repr≤last.1.repr ∧ last.1.repr≤eta.1.repr ∧
    Vendor.R1.treeWeight last.1≤Vendor.R1.treeWeight eta.1 ∧
    (∀ p∈added,lower.1.repr<p.1.1.repr ∧ Vendor.R1.treeWeight p.1.1≤Vendor.R1.treeWeight eta.1) ∧
    (¬encodedSuccessorNormalizationActive (rawNoteEncode lower.1) s ∨
      Vendor.R1.treeWeight last.1+k≤Vendor.R1.treeWeight eta.1) ∧
    1≤s.2.2 ∧
    encodedOneVariableComparisonDomainBound (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))≤s.2.2 ∧
    encodedOneVariableComparisonDomainBound
      (oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E))≤s.2.2 ∧
    ∀ x : Nat, s.2.2≤x →
      actualPrincipalWordRun (comparisonRawWord (w++[(eta,c)])) (actualFixedLimitProfileEval E x)=
        actualPrincipalWordRun (comparisonRawWord ((w++added)++[(last,c)])) (actualFixedLimitProfileEval E x)

end LogicLineages.OrdinalComparison
