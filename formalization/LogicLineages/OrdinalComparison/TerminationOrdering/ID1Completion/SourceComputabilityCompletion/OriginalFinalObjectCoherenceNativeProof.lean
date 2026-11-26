module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceNativeProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedWindowEquivalence NumberedLeastCodeRepresentative
open NumberedPrimaryWeakening NumberedPrimarySubstitution NumberedUniverseBindingTargets
open UniformCertificateCompletion OriginalFinalObjectCoherence OriginalRawObjectTransport
open OriginalFinalObjectCoherenceCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Bottom erasure is good on every type actually used by its source.
The removed binder type itself need not be in the finite window. -/
theorem eraseUniverse (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (sigma : Ty)
    (q : Packed (Fin n) arity (sigma :: Gamma)) (hq : InUniverse symbols S q.2) :
    InUniverse symbols S
      (substitutePacked (singleSubstitution (.bottom sigma)) q).2 := by
  exact NumberedUniverseBindingProof.substituteGood
    (fun tau => tau ∈ S) (HeadInWindow arity symbols S) q.2 Gamma
    (singleSubstitution (.bottom sigma)) hq
    (NumberedBottomVariableProof.actualBottomOrVariableGood (Fin n) arity
      (fun tau => tau ∈ S) (HeadInWindow arity symbols S) (sigma :: Gamma) Gamma
      (singleSubstitution (.bottom sigma))
      (NumberedBottomVariableProof.actualSingleBottomOrVariable (Fin n) arity Gamma sigma))

/-- An attained representative of the original weakening returns, after
actual bottom erasure, to the original primary class. No strict step or
positive path is manufactured out of primary equivalence. -/
theorem erasedRepresentative (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty)
    (hS : SubtypeClosed (fun tau => tau ∈ S)) (sigma : Ty)
    (q : Packed (Fin n) arity Gamma) (hq : InUniverse symbols S q.2) :
    ∃ r : Packed (Fin n) arity (sigma :: Gamma),
      representativeCode symbols S (renamePacked (Renaming.weaken Gamma sigma) q) =
        packedNumber r ∧
      representativeCode symbols S (substitutePacked (singleSubstitution (.bottom sigma)) r) =
        representativeCode symbols S q := by
  let shifted := renamePacked (Renaming.weaken Gamma sigma) q
  have hshifted : InUniverse symbols S shifted.2 :=
    NumberedUniverseBindingProof.renameGood
      (fun tau => tau ∈ S) (HeadInWindow arity symbols S) q.2 (sigma :: Gamma)
      (Renaming.weaken Gamma sigma) hq
  obtain ⟨r,hprimary,hcode⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
    n arity symbols S hS (sigma :: Gamma) shifted hshifted
  have hr : InUniverse symbols S r.2 :=
    (NumberedWindowEquivalenceProof.actualPrimaryConfinement
      (Fin n) arity symbols S (sigma :: Gamma) shifted r hprimary).mp hshifted
  have herased := eraseUniverse n arity symbols S Gamma sigma r hr
  have htransport := NumberedPrimarySubstitutionProof.actualPrimarySubstitution
    (Fin n) arity symbols S (sigma :: Gamma) Gamma
    (singleSubstitution (.bottom sigma)) shifted r hprimary
  have hcancel : substitutePacked (singleSubstitution (.bottom sigma)) shifted = q :=
    NumberedPrimaryWeakeningProof.packedWeakeningCancel sigma q
  rw [hcancel] at htransport
  have heq := (NumberedLeastCodeRepresentativeProof.representativeEquality
    n arity symbols S hS Gamma q
      (substitutePacked (singleSubstitution (.bottom sigma)) r) hq herased).mpr htransport
  exact ⟨r,hcode,heq.symm⟩

theorem actualOriginalFinalObjectCanonicalCancellation :
    OriginalFinalObjectCoherenceTargets.ActualOriginalFinalObjectCanonicalCancellation := by
  intro n arity p hp symbols S Gamma table hS sigma tau q hq
  obtain ⟨r,hcode,herased⟩ := erasedRepresentative
    n arity symbols S Gamma hS sigma ⟨tau,q⟩ hq
  change canonicalObject p (OrdinaryArithmeticQuotient.contextCode symbols S table)
    (evaluate eraseObjectRaw (List.Vector.ofFn ![
      canonicalObject p (OrdinaryArithmeticQuotient.contextCode symbols S table)
        (evaluate shiftObjectRaw (List.Vector.ofFn ![typeNumber sigma,
          ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩)]))])) =
    canonicalObject p (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩))
  rw [shiftObjectOnPacked n arity Gamma sigma ⟨tau,q⟩,
    canonicalOnPacked n arity p hp symbols S (sigma :: Gamma) table hS,
    hcode,eraseObjectOnPacked n arity Gamma sigma r,
    canonicalOnPacked n arity p hp symbols S Gamma table hS,
    canonicalOnPacked n arity p hp symbols S Gamma table hS,herased]

theorem actualOriginalFinalObjectRankInvariance :
    OriginalFinalObjectCoherenceTargets.ActualOriginalFinalObjectRankInvariance := by
  intro n arity p hp symbols S Gamma table hS tau q hq
  obtain ⟨r,hprimary,hcode⟩ := NumberedLeastCodeRepresentativeProof.representativeAttained
    n arity symbols S hS Gamma ⟨tau,q⟩ hq
  change evaluate variableRankObjectRaw (List.Vector.ofFn ![
    canonicalObject p (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩))]) =
    evaluate variableRankObjectRaw (List.Vector.ofFn ![
      ContextUniform.objectCode Gamma (packedNumber ⟨tau,q⟩)])
  rw [canonicalOnPacked n arity p hp symbols S Gamma table hS,hcode,
    rankObjectOnPacked n arity Gamma r,rankObjectOnPacked n arity Gamma ⟨tau,q⟩]
  exact (NumberedVariableCountProof.actualPrimaryVariableCount
    (Fin n) arity symbols S Gamma ⟨tau,q⟩ r hprimary).symm

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalObjectCoherenceNativeProof
