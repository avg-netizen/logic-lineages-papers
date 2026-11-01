module
public import LogicLineages.OrdinalComparison.SourcePeakWordDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def SourcePeakWordCodeProgram : Prop := Primrec₂ encodedSourcePeakWord ∧
  ∀ rho : NONote, ∀ E : FixedLimitPositiveExpr,
    encodedSourcePeakWord (rawNoteEncode rho.1) (positiveExprEncode E)=
      oneVariableComparisonEncode (comparisonSourcePeakWord rho E)

def SourcePeakWordLiteralShape : Prop :=
  (∀ rho : NONote, (comparisonTypedPrincipalBlocks rho).map Subtype.val=principalExponentBlocks rho.1) ∧
  (∀ (es : List NONote) (c : Nat), comparisonRawWord (comparisonTypedPrincipalWord es c)=
    principalKernelWord (es.map Subtype.val) c) ∧
  ∀ rho : NONote, ∀ E : FixedLimitPositiveExpr,
    comparisonLiteralSourceHeadCount (comparisonSourcePeakWord rho E)=comparisonPositiveSourceHeadCount E

/-- Literal original P/R child, all reached kernel inputs, actual peak VALUE
and original collapse/count identity. The closed norm shift contributes no
original h nodes. No source compiler/domain/peak-value premise is supplied. -/
def ActualSourcePeakWordSemantics : Prop :=
  ∀ rho : NONote, Order.IsSuccLimit rho.1.repr → rho.1.repr<epsilonZero →
  ∀ E : FixedLimitPositiveExpr, fixedLimitProfileBelow epsilonZero E → positiveExprHasInput E=true →
    oneVariableComparisonValid (comparisonSourcePeakWord rho E) ∧
    ∀ x : Nat,
      oneVariableComparisonDomainAt (comparisonSourcePeakWord rho E) x ∧
      actualOneVariableComparisonValue (comparisonSourcePeakWord rho E) x=
        actualCollectedTagPeak rho (collectedPositiveNormalize E) x ∧
      let word := comparisonRawWord (comparisonTypedPrincipalWord (comparisonTypedPrincipalBlocks rho) 0)
      let run := actualPrincipalWordRun word (Vendor.R1.treeWeight rho.1+actualFixedLimitProfileEval E x)
      0<run.2 ∧ actualCollapse (rho.1.repr+(actualFixedLimitProfileEval E x : Ordinal))=run.1+run.2

def SourcePeakWordFiniteCarrier : Prop :=
  ∀ (budget : Nat) (rho : NONote), Vendor.R1.treeWeight rho.1≤budget →
    ∀ p∈comparisonTypedPrincipalWord (comparisonTypedPrincipalBlocks rho) 0,
      p.1∈comparisonTypedPrincipalBlocks rho ∧ rawNoteEncode p.1.1∈encodedNormalNormBall budget

def FullActualSourcePeakWord : Prop := SourcePeakWordCodeProgram ∧ SourcePeakWordLiteralShape ∧
  ActualSourcePeakWordSemantics ∧ SourcePeakWordFiniteCarrier

end LogicLineages.OrdinalComparison.Targets
