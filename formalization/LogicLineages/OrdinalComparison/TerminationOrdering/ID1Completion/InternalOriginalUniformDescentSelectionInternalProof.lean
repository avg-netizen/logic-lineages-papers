module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedBoundedDescentNormalizerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection InternalOriginalUniformDescentSelectionTargets
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalOriginalTypedCarrierSupportProof (atValue atRecover)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalParameterizedBoundedDescentNormalizer
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Recover all four original graph factors from the literal ternary checker.
Both binary leaves and transition receive the identical symbolic parameter. -/
theorem typedRecover (R V member : Program 2) (value typ parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (typedAccepted R V member value typ parameter))) :
    Nonempty (Derivation body Gamma (typedFactors R V member value typ parameter)) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term α :=
    Fin.cons value (Fin.cons typ (Fin.cons parameter Fin.elim0))
  have hm := conjunctionRecover _ _ xs h
  have hv := conjunctionRecover _ _ xs (andRight hm)
  have ht := conjunctionRecover _ _ xs (andRight hv)
  have hl := sameRightRecover (leftOf (.projection 0)) (.projection 1)
    typ xs (andLeft ht) (projectionValue 1 xs)
  have hf := sameRightRecover
    (.composition (transition R V) ![.projection 0,.projection 2])
    (.projection 0) value xs (andRight ht) (projectionValue 0 xs)
  exact andIntro
    (binaryRecover member (.projection 1) (.projection 2) (suc z) typ parameter xs
      (andLeft hm) (projectionValue 1 xs) (projectionValue 2 xs))
    (andIntro
      (binaryRecover V (.projection 0) (.projection 2) (suc z) value parameter xs
        (andLeft hv) (projectionValue 0 xs) (projectionValue 2 xs))
      (andIntro (atRecover InternalUnpair.left 0 typ xs hl)
        (binaryRecover (transition R V) (.projection 0) (.projection 2) value value parameter xs
          hf (projectionValue 0 xs) (projectionValue 2 xs))))

/-- Introduce the actual checker from membership, source validity, the
original value tag, and fixedness of the actual parameterized transition. -/
theorem typedAccept (R V member : Program 2) (value typ parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (typedFactors R V member value typ parameter))) :
    Nonempty (Derivation body Gamma (typedAccepted R V member value typ parameter)) := by
  let xs : Fin 3 → OrdinaryArithmetic.Term α :=
    Fin.cons value (Fin.cons typ (Fin.cons parameter Fin.elim0))
  have hm := binaryValue member (.projection 1) (.projection 2) (suc z) typ parameter xs
    (andLeft h) (projectionValue 1 xs) (projectionValue 2 xs)
  have hv := binaryValue V (.projection 0) (.projection 2) (suc z) value parameter xs
    (andLeft (andRight h)) (projectionValue 0 xs) (projectionValue 2 xs)
  have hl := atValue InternalUnpair.left 0 typ xs (andLeft (andRight (andRight h)))
  have hf := binaryValue (transition R V) (.projection 0) (.projection 2) value value parameter xs
    (andRight (andRight (andRight h))) (projectionValue 0 xs) (projectionValue 2 xs)
  exact conjunctionAccept _ _ xs hm
    (conjunctionAccept _ _ xs hv
      (conjunctionAccept _ _ xs
        (sameAccept (leftOf (.projection 0)) (.projection 1) typ xs hl (projectionValue 1 xs))
        (sameAccept (.composition (transition R V) ![.projection 0,.projection 2])
          (.projection 0) value xs hf (projectionValue 0 xs))))

/-- Exact-one input validity selects the actual value-bounded branch. The
parameter is carried as a separate input and is never used as the fuel. -/
theorem boundedRecover (R V : Program 2) (out input parameter : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input parameter)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input parameter))) :
    Nonempty (Derivation body Gamma (normalizerGraph R V out input parameter)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := Fin.cons input (Fin.cons parameter Fin.elim0)
  exact successorBranchElim (InternalApplicationValidityStack.exactOne V) R
    (normalizer R V) out z xs
    (sameAccept V (InternalLessThan.constantOne 2) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hd

/-- The checked parameterized normalizer preserves exact-one validity at
the same parameter; no external calibration is used in this derivation. -/
theorem descentValidity (R V : Program 2) (out input parameter : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input parameter)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input parameter))) :
    Nonempty (Derivation body Gamma (validGraph V out parameter)) := by
  obtain ⟨hb⟩ := boundedRecover R V out input parameter hd hv
  obtain ⟨h⟩ := InternalParameterizedBoundedDescentNormalizerProof.actualOriginalParameterizedBoundedDescentNormalizerValidity
    body R V α Gamma out input parameter
  obtain ⟨hv⟩ := hv
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hb) hv⟩

/-- Preserve the original left tag of the value, independently of the
parameter used by the binary validity and representative leaves. -/
theorem descentLeft (R V : Program 2) (out input typ parameter : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input parameter)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input parameter)))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  obtain ⟨hb⟩ := boundedRecover R V out input parameter hd hv
  obtain ⟨h⟩ := InternalParameterizedBoundedDescentNormalizerProof.actualOriginalParameterizedBoundedDescentNormalizerLeft
    body R V α Gamma out input typ parameter
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hb) hl⟩

/-- The actual transition, with its unchanged parameter, fixes the output
of the selected bounded branch. This is not a representative-leaf premise. -/
theorem descentFixed (R V : Program 2) (out input parameter : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input parameter)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input parameter))) :
    Nonempty (Derivation body Gamma (transitionGraph R V out out parameter)) := by
  obtain ⟨hb⟩ := boundedRecover R V out input parameter hd hv
  obtain ⟨h⟩ := InternalParameterizedBoundedDescentNormalizerProof.actualOriginalParameterizedBoundedDescentNormalizerFixedPoint
    body R V α Gamma out input parameter
  exact ⟨Derivation.implicationElimination h hb⟩

/-- Combine the three independently established consequences of the
literal fallback graph, input validity, and original input-tag graph. -/
theorem descentInvariant (R V : Program 2) (out input typ parameter : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (outputPremises R V out input typ parameter))) :
    Nonempty (Derivation body Gamma (outputInvariant R V out typ parameter)) := by
  have hd := andLeft h
  have hv := andLeft (andRight h)
  have hl := andRight (andRight h)
  exact andIntro (descentValidity R V out input parameter hd hv)
    (andIntro (descentLeft R V out input typ parameter hd hv hl)
      (descentFixed R V out input parameter hd hv))

theorem actualParameterizedTypedFactorization : ActualParameterizedTypedFactorization := by
  intro body R V member α Delta value typ parameter
  obtain ⟨hf⟩ := typedRecover (body := body)
    (Gamma := typedAccepted R V member value typ parameter :: Delta) R V member value typ parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := typedAccept (body := body)
    (Gamma := typedFactors R V member value typ parameter :: Delta) R V member value typ parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualParameterizedRepresentativeInvariant : ActualParameterizedRepresentativeInvariant := by
  intro body R V α Delta out input typ parameter
  obtain ⟨h⟩ := descentInvariant (body := body)
    (Gamma := outputPremises R V out input typ parameter :: Delta) R V out input typ parameter
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

theorem actualParameterizedTypedOutput : ActualParameterizedTypedOutput := by
  intro body R V member α Delta out input typ parameter
  let P := typedOutputPremises R V member out input typ parameter
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := typedAccept R V member out typ parameter
    (andIntro (andRight hp) (descentInvariant R V out input typ parameter (andLeft hp)))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformDescentSelectionInternalProof
