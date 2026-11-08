module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBoundedDescentNormalizerProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionInternalProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalCanonicalDescentSelection InternalCanonicalDescentSelectionTargets
open InternalApplicationCertificateConstructors
open InternalOriginalTypedCarrierSupportProof (atValue atRecover)
open InternalStructuralEndpointGuardSupportProof (sameRightRecover)
open InternalApplicationStepPeelSupportProof InternalControlGraphSupportProof
open InternalAcceptanceConjunctionProof InternalAcceptanceBranchProof
open InternalBoundedDescentNormalizer
open InternalTagArithmeticSyntaxProof (suc z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {α : Type} {Gamma : List (Formula α)}

/-- Recover the four actual graph factors from the literal new checker. -/
theorem typedRecover (R V member : Program 1) (value typ : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (typedAccepted R V member value typ))) :
    Nonempty (Derivation body Gamma (typedFactors R V member value typ)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := Fin.cons value (Fin.cons typ Fin.elim0)
  have hm := conjunctionRecover _ _ xs h
  have hv := conjunctionRecover _ _ xs (andRight hm)
  have ht := conjunctionRecover _ _ xs (andRight hv)
  have hl := sameRightRecover (leftOf (.projection 0)) (.projection 1)
    typ xs (andLeft ht) (projectionValue 1 xs)
  have hf := sameRightRecover
    (.composition (transition R V) (fun _ : Fin 1 => .projection 0))
    (.projection 0) value xs (andRight ht) (projectionValue 0 xs)
  exact andIntro (atRecover member 1 (suc z) xs (andLeft hm))
    (andIntro (atRecover V 0 (suc z) xs (andLeft hv))
      (andIntro (atRecover InternalUnpair.left 0 typ xs hl)
        (atRecover (transition R V) 0 value xs hf)))

/-- Introduce the literal checker without an old canonical-typed leaf. -/
theorem typedAccept (R V member : Program 1) (value typ : OrdinaryArithmetic.Term α)
    (h : Nonempty (Derivation body Gamma (typedFactors R V member value typ))) :
    Nonempty (Derivation body Gamma (typedAccepted R V member value typ)) := by
  let xs : Fin 2 → OrdinaryArithmetic.Term α := Fin.cons value (Fin.cons typ Fin.elim0)
  have hm := atValue member 1 (suc z) xs (andLeft h)
  have hv := atValue V 0 (suc z) xs (andLeft (andRight h))
  have hl := atValue InternalUnpair.left 0 typ xs (andLeft (andRight (andRight h)))
  have hf := atValue (transition R V) 0 value xs (andRight (andRight (andRight h)))
  exact conjunctionAccept _ _ xs hm
    (conjunctionAccept _ _ xs hv
      (conjunctionAccept _ _ xs
        (sameAccept (leftOf (.projection 0)) (.projection 1) typ xs hl (projectionValue 1 xs))
        (sameAccept (.composition (transition R V) (fun _ : Fin 1 => .projection 0))
          (.projection 0) value xs hf (projectionValue 0 xs))))

/-- Exact-one input validity selects the actual bounded branch internally. -/
theorem boundedRecover (R V : Program 1) (out input : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input))) :
    Nonempty (Derivation body Gamma (normalizerGraph R V out input)) := by
  let xs : Fin 1 → OrdinaryArithmetic.Term α := Fin.cons input Fin.elim0
  exact successorBranchElim (InternalApplicationValidityStack.exactOne V) R
    (normalizer R V) out z xs
    (sameAccept V (InternalLessThan.constantOne 1) (suc z) xs hv
      (InternalLessThanSupportProof.oneConstantValue xs)) hd

/-- Consume the already checked B validity law, not external calibration. -/
theorem descentValidity (R V : Program 1) (out input : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input))) :
    Nonempty (Derivation body Gamma (validGraph V out)) := by
  obtain ⟨hb⟩ := boundedRecover R V out input hd hv
  obtain ⟨h⟩ := InternalBoundedDescentNormalizerProof.actualOriginalBoundedDescentNormalizerValidity
    body R V α Gamma out input
  obtain ⟨hv⟩ := hv
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hb) hv⟩

/-- Consume checked B left preservation at the same symbolic tag. -/
theorem descentLeft (R V : Program 1) (out input typ : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input)))
    (hl : Nonempty (Derivation body Gamma (leftGraph typ input))) :
    Nonempty (Derivation body Gamma (leftGraph typ out)) := by
  obtain ⟨hb⟩ := boundedRecover R V out input hd hv
  obtain ⟨h⟩ := InternalBoundedDescentNormalizerProof.actualOriginalBoundedDescentNormalizerLeft
    body R V α Gamma out input typ
  obtain ⟨hl⟩ := hl
  exact ⟨Derivation.implicationElimination (Derivation.implicationElimination h hb) hl⟩

/-- Checked B stabilization supplies precisely the T-fixed graph. -/
theorem descentFixed (R V : Program 1) (out input : OrdinaryArithmetic.Term α)
    (hd : Nonempty (Derivation body Gamma (representativeGraph R V out input)))
    (hv : Nonempty (Derivation body Gamma (validGraph V input))) :
    Nonempty (Derivation body Gamma (transitionGraph R V out out)) := by
  obtain ⟨hb⟩ := boundedRecover R V out input hd hv
  obtain ⟨h⟩ := InternalBoundedDescentNormalizerProof.actualOriginalBoundedDescentNormalizerFixedPoint
    body R V α Gamma out input
  exact ⟨Derivation.implicationElimination h hb⟩

theorem actualOriginalCanonicalDescentTypedFactorization :
    ActualOriginalCanonicalDescentTypedFactorization := by
  intro body R V member α Delta value typ
  obtain ⟨hf⟩ := typedRecover (body := body)
    (Gamma := typedAccepted R V member value typ :: Delta) R V member value typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨hb⟩ := typedAccept (body := body)
    (Gamma := typedFactors R V member value typ :: Delta) R V member value typ
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hf)
    (Derivation.implicationIntroduction hb)⟩

theorem actualOriginalCanonicalDescentValidity : ActualOriginalCanonicalDescentValidity := by
  intro body R V α Delta out input
  obtain ⟨h⟩ := descentValidity (body := body)
    (Gamma := validGraph V input :: representativeGraph R V out input :: Delta) R V out input
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem actualOriginalCanonicalDescentLeft : ActualOriginalCanonicalDescentLeft := by
  intro body R V α Delta out input typ
  obtain ⟨h⟩ := descentLeft (body := body)
    (Gamma := leftGraph typ input :: validGraph V input :: representativeGraph R V out input :: Delta)
    R V out input typ
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction
    (Derivation.implicationIntroduction (Derivation.implicationIntroduction h))⟩

theorem actualOriginalCanonicalDescentFixedPoint : ActualOriginalCanonicalDescentFixedPoint := by
  intro body R V α Delta out input
  obtain ⟨h⟩ := descentFixed (body := body)
    (Gamma := validGraph V input :: representativeGraph R V out input :: Delta) R V out input
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction h)⟩

theorem actualOriginalCanonicalDescentTypedOutput : ActualOriginalCanonicalDescentTypedOutput := by
  intro body R V member α Delta out input typ
  let P := outputPremises R V member out input typ
  have hp : Nonempty (Derivation body (P :: Delta) P) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have hd := andLeft hp
  have hv := andLeft (andRight hp)
  have hl := andLeft (andRight (andRight hp))
  have hm := andRight (andRight (andRight hp))
  obtain ⟨h⟩ := typedAccept R V member out typ
    (andIntro hm (andIntro (descentValidity R V out input hd hv)
      (andIntro (descentLeft R V out input typ hd hv hl) (descentFixed R V out input hd hv))))
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionInternalProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalCanonicalDescentSelectionInternalProof
