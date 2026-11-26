module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSingleBottomLeastTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSingleBottomLeastProof
open Source OrdinaryArithmeticQuotient OrdinaryArithmeticCarrier PositiveArithmeticOperators
open PositiveArithmeticLeastSet PositiveArithmeticAccessibility NumberedRewriteSyntax NumberedRewriteReduction
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedPrimarySubstitution

theorem actualScalarLeastSingleBottom : SourceSingleBottomLeastTargets.ActualScalarLeastSingleBottom := by
  intro n arity Gamma context ctx scalarOld scalarNew hc hclosed sigma hcalOld hcalNew q hq
  let erased := substitutePacked (singleSubstitution (.bottom sigma)) q
  have hgood : NumberedUniverseBindingTargets.GoodSubstitution (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) (singleSubstitution (AuxTerm.bottom (Symbol := Fin n) (arity := arity) (Gamma := Gamma) sigma)) :=
    NumberedBottomVariableProof.actualBottomOrVariableGood (Fin n) arity
      (fun t => t ∈ ctx.1.2) (HeadInWindow arity ctx.1.1 ctx.1.2) (sigma :: Gamma) Gamma
      (singleSubstitution (.bottom sigma))
      (NumberedBottomVariableProof.actualSingleBottomOrVariable (Fin n) arity Gamma sigma)
  have he : InUniverse ctx.1.1 ctx.1.2 erased.2 :=
    NumberedUniverseBindingProof.substituteGood (fun t => t ∈ ctx.1.2)
      (HeadInWindow arity ctx.1.1 ctx.1.2) q.2 Gamma (singleSubstitution (.bottom sigma)) hq hgood
  have hcarrierOld : encodedScalar n arity Gamma context (representativeCode ctx.1.1 ctx.1.2 erased) := by
    refine ⟨ctx,hc,?_⟩
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed Gamma _).mpr ⟨erased,he,rfl⟩
  have hcarrierNew : encodedScalar n arity (sigma :: Gamma) context (representativeCode ctx.1.1 ctx.1.2 q) := by
    refine ⟨ctx,hc,?_⟩
    exact (NumberedNumericCarrierProof.canonicalCarrierTestCorrect n arity ctx.1.1 ctx.1.2 hclosed (sigma :: Gamma) _).mpr ⟨q,hq,rfl⟩
  have hOld := PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalarOld context
    (encodedScalar n arity Gamma context) (encodedR n arity Gamma context) hcalOld
    (SourceArithmeticAccessibilityProof.encodedScalarPreservation n arity Gamma context ⟨ctx,hc,hclosed⟩)
    (representativeCode ctx.1.1 ctx.1.2 erased)
  have hNew := PositiveArithmeticAccessibilityProof.preservedCarrierAccessibility scalarNew context
    (encodedScalar n arity (sigma :: Gamma) context) (encodedR n arity (sigma :: Gamma) context) hcalNew
    (SourceArithmeticAccessibilityProof.encodedScalarPreservation n arity (sigma :: Gamma) context ⟨ctx,hc,hclosed⟩)
    (representativeCode ctx.1.1 ctx.1.2 q)
  have htransport := NumberedBottomVariableAccessibilityProof.actualSingleBottomAccessibilityEquivalence
    n arity ctx.1.1 ctx.1.2 hclosed (NumberedCopyCertificate.tableAbove ctx.2) Gamma sigma q hq
  constructor
  · intro hm
    have ha := (hNew.mp hm).2
    have hactual := Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (sigma :: Gamma) context ctx hc x y).mpr h) ha
    have herased := htransport.mp hactual
    exact hOld.mpr ⟨hcarrierOld,Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc x y).mp h) herased⟩
  · intro hm
    have ha := (hOld.mp hm).2
    have hactual := Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity Gamma context ctx hc x y).mpr h) ha
    have horiginal := htransport.mpr hactual
    exact hNew.mpr ⟨hcarrierNew,Subrelation.accessible (fun {y x} h =>
      (SourceComputabilityArrowLeastSupportProof.relationCalibration n arity (sigma :: Gamma) context ctx hc x y).mp h) horiginal⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSingleBottomLeastProof
