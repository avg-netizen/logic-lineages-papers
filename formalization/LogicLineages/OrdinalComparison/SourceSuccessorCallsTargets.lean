module
public import LogicLineages.OrdinalComparison.SourceKernelCallsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

/-- Literal combined replacement on the ACTUAL source pair: drop original
higher outer occurrence, remove opposite lower occurrence, and retain every
new strictly higher kernel occurrence. No intermediate rewritten call. -/
def ActualBoundedHigherReplacementChild : Prop :=
  ∀ (budget : Nat) (eta lower : NONote),
    Vendor.R1.treeWeight eta.1≤budget → Vendor.R1.treeWeight lower.1≤budget →
  ∀ (w v added : List (NONote × Nat)) (c d : Nat) (E F : FixedLimitPositiveExpr),
    (∀ p∈added,lower.1.repr<p.1.1.repr ∧ Vendor.R1.treeWeight p.1.1≤budget) →
    Relation.TransGen (comparisonLiteralPairStep budget)
      (comparisonLiteralInner (w++added) E,comparisonLiteralInner v F)
      (.range (w++[(eta,c)]) E,.range (v++[(lower,d)]) F)

/-- The actual CODED successor pass returns original source children in the
strict transitive pair relation. Both equal-final and higher-limit branches
are paid; no claim that the rewritten intermediate pair decreases. -/
def ActualComputedSuccessorChildCalls : Prop :=
  ∀ (budget : Nat) (w v : List (NONote × Nat)) (E F : FixedLimitPositiveExpr)
    (eta lower : NONote) (c d : Nat),
    oneVariableComparisonValid (.range (w++[(eta,c)]) E) →
    Vendor.R1.treeWeight eta.1≤budget → Vendor.R1.treeWeight lower.1≤budget →
    0<lower.1.repr → lower.1.repr<eta.1.repr →
    ∃ (added : List (NONote × Nat)) (last : NONote),
      (encodedSuccessorNormalization (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode lower.1) c).1=
          oneVariableComparisonEncode (.range ((w++added)++[(last,c)]) E) ∧
      (encodedSuccessorNormalization (oneVariableComparisonEncode (.range w E))
        (rawNoteEncode eta.1) (rawNoteEncode lower.1) c).2.1=rawNoteEncode last.1 ∧
      oneVariableComparisonValid (.range ((w++added)++[(last,c)]) E) ∧
      lower.1.repr≤last.1.repr ∧
      (last.1.repr=lower.1.repr ∨ Order.IsSuccLimit last.1.repr) ∧
      (last.1.repr=lower.1.repr →
        Relation.TransGen (comparisonLiteralPairStep budget)
          (comparisonLiteralInner (w++added) E,comparisonLiteralInner v F)
          (.range (w++[(eta,c)]) E,.range (v++[(lower,d)]) F)) ∧
      (lower.1.repr<last.1.repr →
        Relation.TransGen (comparisonLiteralPairStep budget)
          (.range ((w++added)++[(last,c)]) E,comparisonLiteralInner v F)
          (.range (w++[(eta,c)]) E,.range (v++[(lower,d)]) F))

def FullActualCombinedSuccessorChildCalls : Prop :=
  ActualBoundedHigherReplacementChild ∧ ActualComputedSuccessorChildCalls

end LogicLineages.OrdinalComparison.Targets
