module
public import LogicLineages.OrdinalComparison.SourceKernelCallsDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def ActualOuterStripProgram : Prop := Primrec encodedComparisonStripOuter ∧
  ∀ (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr),
    encodedComparisonStripOuter (oneVariableComparisonEncode (.range (w++[(eta,c)]) E))=
      oneVariableComparisonEncode (comparisonLiteralInner w E)

def ActualOuterStripShapeSemantics : Prop :=
  (∀ w E, comparisonLiteralSourceHeadCount (comparisonLiteralInner w E)=comparisonPositiveSourceHeadCount E ∧
    comparisonAuxiliarySourceWord (comparisonLiteralInner w E)=w) ∧
  (∀ w eta c E, oneVariableComparisonValid (.range (w++[(eta,c)]) E) →
    oneVariableComparisonValid (comparisonLiteralInner w E)) ∧
  ∀ (w : List (NONote × Nat)) (eta : NONote) (c : Nat) (E : FixedLimitPositiveExpr) (x : Nat),
    actualOneVariableComparisonValue (.range (w++[(eta,c)]) E) x=
      actualSuffixKernel (Ordinal.omega0^eta.1.repr) c
        (actualOneVariableComparisonValue (comparisonLiteralInner w E) x)

def LiteralPairTransitiveStepWellFounded : Prop :=
  ∀ budget, WellFounded (Relation.TransGen (comparisonLiteralPairStep budget))

/-- Both actual equal-principal recursive arguments. The two removed outer
occurrences pay a finite strict descent, rather than an assumed comparison key. -/
def ActualEqualOuterChildCall : Prop :=
  ∀ (budget : Nat) (eta : NONote), Vendor.R1.treeWeight eta.1≤budget →
  ∀ (w v : List (NONote × Nat)) (c d : Nat) (E F : FixedLimitPositiveExpr),
    Relation.TransGen (comparisonLiteralPairStep budget)
      (comparisonLiteralInner w E,comparisonLiteralInner v F)
      (.range (w++[(eta,c)]) E,.range (v++[(eta,d)]) F)

/-- Actual mixed-limit recursive child X versus B; only the lower outer
occurrence is removed. This statement does not assert comparison correctness. -/
def ActualMixedLimitChildCall : Prop :=
  ∀ (budget : Nat) (eta : NONote), Vendor.R1.treeWeight eta.1≤budget →
  ∀ (X : OneVariableComparisonExpr) (v : List (NONote × Nat)) (d : Nat) (F : FixedLimitPositiveExpr),
    comparisonLiteralPairStep budget (X,comparisonLiteralInner v F) (X,.range (v++[(eta,d)]) F)

def FullActualOuterKernelChildCalls : Prop := ActualOuterStripProgram ∧ ActualOuterStripShapeSemantics ∧
  LiteralPairTransitiveStepWellFounded ∧ ActualEqualOuterChildCall ∧ ActualMixedLimitChildCall

end LogicLineages.OrdinalComparison.Targets
