module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportTypedProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedNumericCarrier NumberedPrimarySubstitution NumberedUniverseBindingTargets
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open OriginalClassContextPrefixNative
open OriginalActiveClassKernelCalibrationSupportProof
open OriginalClassContextNativeProof (sourceOnPacked)
open OriginalRawSyntaxTransport (prefixErasure)
open OriginalRankGuardedRepresentativeEvaluationProof (packedRank)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem prefixBottomOrVariable (n : Nat) (arity : Fin n → Nat)
    (binders Gamma : List Ty) (sigma : Ty) :
    NumberedBottomVariable.BottomOrVariable
      (prefixErasure (Symbol := Fin n) (arity := arity) binders Gamma sigma) := by
  induction binders with
  | nil => exact NumberedBottomVariableProof.actualSingleBottomOrVariable (Fin n) arity Gamma sigma
  | cons tau binders ih =>
    exact NumberedBottomVariableProof.actualLiftBottomOrVariable (Fin n) arity
      (binders ++ sigma :: Gamma) (binders ++ Gamma) tau (prefixErasure binders Gamma sigma) ih

theorem prefixEraseUniverse (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S binders Gamma : List Ty) (sigma : Ty)
    (q : Packed (Fin n) arity (binders ++ sigma :: Gamma)) (hq : InUniverse symbols S q.2) :
    InUniverse symbols S (substitutePacked (prefixErasure binders Gamma sigma) q).2 := by
  exact NumberedUniverseBindingProof.substituteGood
    (fun tau => tau ∈ S) (HeadInWindow arity symbols S) q.2 (binders ++ Gamma)
    (prefixErasure binders Gamma sigma) hq
    (NumberedBottomVariableProof.actualBottomOrVariableGood (Fin n) arity
      (fun tau => tau ∈ S) (HeadInWindow arity symbols S) (binders ++ sigma :: Gamma) (binders ++ Gamma)
      (prefixErasure binders Gamma sigma) (prefixBottomOrVariable n arity binders Gamma sigma))

theorem erasedPackedOnTyped (n : Nat) (arity : Fin n → Nat) (binders Gamma : List Ty)
    (sigma : Ty) (q : Packed (Fin n) arity (binders ++ sigma :: Gamma)) :
    erasedPacked binders sigma (packedNumber q) =
      packedNumber (substitutePacked (prefixErasure binders Gamma sigma) q) := by
  rcases q with ⟨tau,q⟩
  unfold erasedPacked
  rw [OriginalRawObjectTransportEvaluationProof.erasePackedEvaluation]
  simp only [packedNumber,Nat.unpair_pair]
  rw [(OriginalRawSyntaxTransportTypedProof.actualRawSyntaxTypedCalibration n arity binders Gamma sigma tau).2.1 q]
  rfl

theorem typedObservers (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S binders Gamma : List Ty) (sigma : Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (q r : Packed (Fin n) arity (binders ++ sigma :: Gamma))
    (hq : InUniverse symbols S q.2) (hr : InUniverse symbols S r.2)
    (hp : WindowPrimary (Fin n) arity symbols S (binders ++ sigma :: Gamma) q r) :
    sourceValidityValue n arity symbols S (binders ++ Gamma) (erasedPacked binders sigma (packedNumber q)) = 1 ∧
      (sourceValidityValue n arity symbols S (binders ++ Gamma) (erasedPacked binders sigma (packedNumber r)) = 1 ∧
        (targetRepresentativeValue n arity symbols S (binders ++ Gamma) (erasedPacked binders sigma (packedNumber q)) =
          targetRepresentativeValue n arity symbols S (binders ++ Gamma) (erasedPacked binders sigma (packedNumber r)) ∧
          evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
              (List.Vector.ofFn ![erasedPacked binders sigma (packedNumber q)]) =
            evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
              (List.Vector.ofFn ![erasedPacked binders sigma (packedNumber r)]))) := by
  rw [erasedPackedOnTyped n arity binders Gamma sigma q,erasedPackedOnTyped n arity binders Gamma sigma r]
  let eq := substitutePacked (prefixErasure binders Gamma sigma) q
  let er := substitutePacked (prefixErasure binders Gamma sigma) r
  have heq := prefixEraseUniverse n arity symbols S binders Gamma sigma q hq
  have her := prefixEraseUniverse n arity symbols S binders Gamma sigma r hr
  have hep := NumberedPrimarySubstitutionProof.actualPrimarySubstitution
    (Fin n) arity symbols S (binders ++ sigma :: Gamma) (binders ++ Gamma)
    (prefixErasure binders Gamma sigma) q r hp
  refine ⟨sourceOnPacked n arity symbols S (binders ++ Gamma) eq heq,
    sourceOnPacked n arity symbols S (binders ++ Gamma) er her,?_,?_⟩
  · rw [InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked,
      InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked]
    exact (NumberedLeastCodeRepresentativeProof.representativeEquality
      n arity symbols S hS (binders ++ Gamma) eq er heq her).mpr hep
  · rw [packedRank,packedRank]
    exact NumberedVariableCountProof.actualPrimaryVariableCount
      (Fin n) arity symbols S (binders ++ Gamma) eq er hep

theorem actualPrefixErasedClassObservers : PrefixErasedClassObserversLaw := by
  intro n arity symbols S binders Gamma sigma hS seed candidate hs hit
  have hc := (rawClassCharacterization n arity symbols S (binders ++ sigma :: Gamma)
    hS seed candidate hs).mp hit
  cases hdq : decodeUniverse n arity symbols S (binders ++ sigma :: Gamma) seed with
  | none => simp [sourceValidityValue,rawCarrierTest,hdq] at hs
  | some q =>
    obtain ⟨hqn,hq⟩ := (NumberedNumericCarrierProof.numericUniverseDecode
      n arity symbols S (binders ++ sigma :: Gamma) seed q).mp hdq
    cases hdr : decodeUniverse n arity symbols S (binders ++ sigma :: Gamma) candidate with
    | none => simp [sourceValidityValue,rawCarrierTest,hdr] at hc
    | some r =>
      obtain ⟨hrn,hr⟩ := (NumberedNumericCarrierProof.numericUniverseDecode
        n arity symbols S (binders ++ sigma :: Gamma) candidate r).mp hdr
      have hkey := hc.2.2
      rw [← hqn,← hrn,InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked,
        InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked] at hkey
      have hp := (NumberedLeastCodeRepresentativeProof.representativeEquality
        n arity symbols S hS (binders ++ sigma :: Gamma) q r hq hr).mp hkey
      rw [← hqn,← hrn]
      exact typedObservers n arity symbols S binders Gamma sigma hS q r hq hr hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextPrefixNativeProof.actualPrefixErasedClassObservers
