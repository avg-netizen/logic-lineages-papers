module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceWeakeningLeastTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceWeakeningLeastProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedPrimaryWeakening

theorem actualScalarLeastWeakening : SourceWeakeningLeastTargets.ActualScalarLeastWeakening := by
  intro n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma hcalOld hcalNew q hq
  let w := renamePacked (Renaming.weaken Gamma sigma) q
  have hw : InUniverse ctx.1.1 ctx.1.2 w.2 :=
    NumberedUniverseBindingProof.actualRenaming (Fin n) arity (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) Gamma (sigma :: Gamma) q.1 q.2 (Renaming.weaken Gamma sigma) hq
  have hcarrierOld : encodedScalar n arity Gamma context (representativeCode ctx.1.1 ctx.1.2 q) := by
    refine ⟨ctx,hc,?_⟩
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed Gamma _).mpr ⟨q,hq,rfl⟩
  have hcarrierNew : encodedScalar n arity (sigma :: Gamma) context (representativeCode ctx.1.1 ctx.1.2 w) := by
    refine ⟨ctx,hc,?_⟩
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed (sigma :: Gamma) _).mpr ⟨w,hw,rfl⟩
  have hOld := PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalarOld context
    (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) hcalOld
    (SourceArithmeticAccessibilityProof.encodedScalarPreservation n arity Gamma context ⟨ctx,hc,hclosed⟩)
    (representativeCode ctx.1.1 ctx.1.2 q)
  have hNew := PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalarNew context
    (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) hcalNew
    (SourceArithmeticAccessibilityProof.encodedScalarPreservation n arity (sigma :: Gamma) context ⟨ctx,hc,hclosed⟩)
    (representativeCode ctx.1.1 ctx.1.2 w)
  constructor
  · intro hm
    have ha := (hOld.mp hm).2
    have hactual := Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc x y).mpr h) ha
    have hweak := NumberedWeakeningAccessibilityProof.actualWeakeningAccessibilityForward n arity ctx.1.1 ctx.1.2 hclosed
      (NumberedCopyCertificate.tableAbove ctx.2) Gamma sigma q hq hactual
    exact hNew.mpr ⟨hcarrierNew,Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (sigma :: Gamma) context ctx hc x y).mp h) hweak⟩
  · intro hm
    have ha := (hNew.mp hm).2
    have hactual := Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (sigma :: Gamma) context ctx hc x y).mpr h) ha
    have hback := NumberedWeakeningAccessibilityProof.actualWeakeningAccessibilityBackward n arity ctx.1.1 ctx.1.2 hclosed
      (NumberedCopyCertificate.tableAbove ctx.2) Gamma sigma q hq hactual
    exact hOld.mpr ⟨hcarrierOld,Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc x y).mp h) hback⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceWeakeningLeastProof
