module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedNumericDecoding
open NumberedNumericCarrier NumberedPrimarySubstitution
open InternalOriginalStepGuard (sourceValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open OriginalClassContextNativeDefinitions OriginalClassContextNativeTargets
open OriginalActiveClassKernelCalibrationSupportProof
open OriginalFinalObjectCoherenceNativeProof OriginalFinalObjectCoherenceCalibrationProof
open OriginalRankGuardedRepresentativeEvaluationProof (packedRank)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

theorem erasedPackedOnTyped (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (sigma : Ty) (q : Packed (Fin n) arity (sigma :: Gamma)) :
    erasedPacked Gamma sigma (packedNumber q) =
      packedNumber (substitutePacked (singleSubstitution (.bottom sigma)) q) := by
  rw [erasedPacked,eraseObjectOnPacked n arity Gamma sigma q]
  simp [ContextUniform.objectCode]

theorem sourceOnPacked (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (q : Packed (Fin n) arity Gamma)
    (hq : InUniverse symbols S q.2) :
    sourceValidityValue n arity symbols S Gamma (packedNumber q) = 1 := by
  have hd := (NumberedNumericCarrierProof.numericUniverseDecode
    n arity symbols S Gamma (packedNumber q) q).mpr ⟨rfl,hq⟩
  simp [sourceValidityValue,rawCarrierTest,hd]

/-- Native actual primary substitution pays the new observers; no class
invariance or erased-rank equality is supplied as a premise. -/
theorem typedObservers (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma : Ty) (hS : SubtypeClosed (fun tau => tau ∈ S))
    (q r : Packed (Fin n) arity (sigma :: Gamma))
    (hq : InUniverse symbols S q.2) (hr : InUniverse symbols S r.2)
    (hp : WindowPrimary (Fin n) arity symbols S (sigma :: Gamma) q r) :
    sourceValidityValue n arity symbols S Gamma (erasedPacked Gamma sigma (packedNumber q)) = 1 ∧
      (sourceValidityValue n arity symbols S Gamma (erasedPacked Gamma sigma (packedNumber r)) = 1 ∧
        (targetRepresentativeValue n arity symbols S Gamma (erasedPacked Gamma sigma (packedNumber q)) =
          targetRepresentativeValue n arity symbols S Gamma (erasedPacked Gamma sigma (packedNumber r)) ∧
          evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
              (List.Vector.ofFn ![erasedPacked Gamma sigma (packedNumber q)]) =
            evaluate OriginalRawSyntaxTransport.variableRankPackedRaw
              (List.Vector.ofFn ![erasedPacked Gamma sigma (packedNumber r)]))) := by
  rw [erasedPackedOnTyped n arity Gamma sigma q,erasedPackedOnTyped n arity Gamma sigma r]
  let eq := substitutePacked (singleSubstitution (.bottom sigma)) q
  let er := substitutePacked (singleSubstitution (.bottom sigma)) r
  have heq := eraseUniverse n arity symbols S Gamma sigma q hq
  have her := eraseUniverse n arity symbols S Gamma sigma r hr
  have hep := NumberedPrimarySubstitutionProof.actualPrimarySubstitution
    (Fin n) arity symbols S (sigma :: Gamma) Gamma
    (singleSubstitution (.bottom sigma)) q r hp
  refine ⟨sourceOnPacked n arity symbols S Gamma eq heq,
    sourceOnPacked n arity symbols S Gamma er her,?_,?_⟩
  · rw [InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked,
      InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked]
    exact (NumberedLeastCodeRepresentativeProof.representativeEquality
      n arity symbols S hS Gamma eq er heq her).mpr hep
  · rw [packedRank,packedRank]
    exact NumberedVariableCountProof.actualPrimaryVariableCount
      (Fin n) arity symbols S Gamma eq er hep

theorem actualOriginalClassContextErasedObservers : ActualOriginalClassContextErasedObservers := by
  intro n arity symbols S Gamma sigma hS seed candidate hs hit
  have hc := (rawClassCharacterization n arity symbols S (sigma :: Gamma)
    hS seed candidate hs).mp hit
  cases hdq : decodeUniverse n arity symbols S (sigma :: Gamma) seed with
  | none => simp [sourceValidityValue,rawCarrierTest,hdq] at hs
  | some q =>
    obtain ⟨hqn,hq⟩ := (NumberedNumericCarrierProof.numericUniverseDecode
      n arity symbols S (sigma :: Gamma) seed q).mp hdq
    cases hdr : decodeUniverse n arity symbols S (sigma :: Gamma) candidate with
    | none => simp [sourceValidityValue,rawCarrierTest,hdr] at hc
    | some r =>
      obtain ⟨hrn,hr⟩ := (NumberedNumericCarrierProof.numericUniverseDecode
        n arity symbols S (sigma :: Gamma) candidate r).mp hdr
      have hkey := hc.2.2
      rw [← hqn,← hrn,InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked,
        InternalRepresentativeFoldCalibrationSupportProof.targetOnPacked] at hkey
      have hp := (NumberedLeastCodeRepresentativeProof.representativeEquality
        n arity symbols S hS (sigma :: Gamma) q r hq hr).mp hkey
      rw [← hqn,← hrn]
      exact typedObservers n arity symbols S Gamma sigma hS q r hq hr hp
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalClassContextNativeProof
