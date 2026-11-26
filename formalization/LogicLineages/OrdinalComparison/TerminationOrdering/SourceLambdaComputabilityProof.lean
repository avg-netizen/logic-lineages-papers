module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaComputabilityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceConditionalLambdaProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceComputabilityLeastProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableAccessibilityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaComputabilityProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedQuotientPaths

theorem actualLambdaComputability : SourceLambdaComputabilityTargets.ActualLambdaComputability := by
  intro n arity Gamma context ctx scalar hc hclosed hcal sigma tau body hl hinst
  have hb : InUniverse ctx.1.1 ctx.1.2 body := ⟨hl.1.2.2,hl.2⟩
  have hbottom : InUniverse ctx.1.1 ctx.1.2
      (AuxTerm.bottom (Symbol := Fin n) (arity := arity) (Gamma := Gamma) sigma) :=
    ⟨hl.1.2.1,trivial⟩
  have hcbottom := SourceBottomSpineComputabilityProof.actualBottomComputable
    n arity Gamma context ctx scalar hc hclosed hcal sigma hl.1.2.1
  have hinstance := hinst (.bottom sigma) hbottom hcbottom
  have hencoded := SourceComputabilityLeastProof.actualComputabilityAccessible
    n arity Gamma context ctx scalar hc hclosed hcal tau _ hinstance
  have herased : Acc (fun successor source => PositivePath
      (QuotientEdge n arity ctx.1.1 ctx.1.2 (NumberedCopyCertificate.tableAbove ctx.2) Gamma) source successor)
      (representativeCode ctx.1.1 ctx.1.2 ⟨tau,substitute body (singleSubstitution (.bottom sigma))⟩) :=
    Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration
        n arity Gamma context ctx hc x y).mpr h) hencoded
  have hbody := (NumberedBottomVariableAccessibilityProof.actualSingleBottomAccessibilityEquivalence
    n arity ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2)
    Gamma sigma ⟨tau,body⟩ hb).mpr herased
  exact SourceConditionalLambdaProof.actualConditionalLambdaComputability
    n arity Gamma context ctx scalar hc hclosed hcal sigma tau body hl hbody hinst

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceLambdaComputabilityProof
