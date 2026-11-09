module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformStepGuardSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerNormalizedProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalParameterizedQuotientEdgeChecker InternalParameterizedQuotientEdgeCheckerSupportProof
open InternalOriginalUniformDescentSelection (Data validity)
open InternalParameterizedCanonicalResultFold (foldN foldGraph)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalUniformStepGuardSupportProof (stepSourceValidity)
open InternalControlGraphSupportProof InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalApplicationStepPeelSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Actual source validity selects the N branch at the same symbolic p. -/
theorem sourceRecover (data : Data) (out input parameter : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity data) InternalOriginalStepGuard.one input parameter)))
    (hr : Nonempty (Derivation body Gamma (sourceRepresentativeGraph data out input parameter))) :
    Nonempty (Derivation body Gamma (foldGraph data out input parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  exact successorBranchElim (InternalApplicationValidityStack.exactOne (validity data))
    (InternalAcceptance.constantZero 2) (foldN data) out z xs
    (sameAccept (validity data) (InternalLessThan.constantOne 2) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hr

theorem sourceAccept (data : Data) (out input parameter : OTerm α)
    (hv : Nonempty (Derivation body Gamma
      (graph2 (validity data) InternalOriginalStepGuard.one input parameter)))
    (hr : Nonempty (Derivation body Gamma (foldGraph data out input parameter))) :
    Nonempty (Derivation body Gamma (sourceRepresentativeGraph data out input parameter)) := by
  let xs : Fin 2 → OTerm α := Fin.cons input (Fin.cons parameter Fin.elim0)
  exact successorBranchIntro (InternalApplicationValidityStack.exactOne (validity data))
    (InternalAcceptance.constantZero 2) (foldN data) out z xs
    (sameAccept (validity data) (InternalLessThan.constantOne 2) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hr

/-- The source filter disappears because W proves source validity. The
target comparison is already literally the actual N graph on all inputs. -/
theorem normalizedRecover (data : Data) (oldStep : Program 4)
    (x y certificate s t k parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hc : Nonempty (Derivation body Gamma (coreAccepted data oldStep x y certificate parameter))) :
    Nonempty (Derivation body Gamma (normalizedRequirements data oldStep x y s t k parameter)) := by
  have hr := coreRecover data oldStep x y certificate s t k parameter hf hc
  have hw := andLeft hr
  exact andIntro hw
    (andIntro (sourceRecover data x s parameter
      (stepSourceValidity data oldStep s t k parameter hw) (andLeft (andRight hr)))
      (andRight (andRight hr)))

theorem normalizedAccept (data : Data) (oldStep : Program 4)
    (x y certificate s t k parameter : OTerm α)
    (hf : Nonempty (Derivation body Gamma (selectors certificate s t k)))
    (hr : Nonempty (Derivation body Gamma (normalizedRequirements data oldStep x y s t k parameter))) :
    Nonempty (Derivation body Gamma (coreAccepted data oldStep x y certificate parameter)) := by
  have hw := andLeft hr
  exact coreAccept data oldStep x y certificate s t k parameter hf
    (andIntro hw
      (andIntro (sourceAccept data x s parameter
        (stepSourceValidity data oldStep s t k parameter hw) (andLeft (andRight hr)))
        (andRight (andRight hr))))

/-- Rebuild the same core from the original edge constructor itself. -/
theorem normalizedAcceptEncoded (data : Data) (oldStep : Program 4)
    (x y certificate s t k parameter : OTerm α)
    (hc : Nonempty (Derivation body Gamma (graph3 edgeCode certificate s t k)))
    (hr : Nonempty (Derivation body Gamma (normalizedRequirements data oldStep x y s t k parameter))) :
    Nonempty (Derivation body Gamma (coreAccepted data oldStep x y certificate parameter)) :=
  normalizedAccept data oldStep x y certificate s t k parameter
    (edgeSelectors certificate s t k hc) hr

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerNormalizedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedQuotientEdgeCheckerNormalizedProof
