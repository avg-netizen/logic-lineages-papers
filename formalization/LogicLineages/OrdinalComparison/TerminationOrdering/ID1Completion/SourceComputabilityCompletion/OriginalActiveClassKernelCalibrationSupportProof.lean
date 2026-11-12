module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveObservedCalibrationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderSelectionCalibrationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationSupportProof
open Source NumberedRewriteReduction NumberedFiniteUniverse NumberedFinitePrimaryClass
open NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedNumericDecoding
open InternalOriginalStepGuard (sourceValidityValue targetValidityValue)
open InternalQuotientEdgeChecker (targetRepresentativeValue)
open InternalOriginalUniformParameterLeaves OriginalTransparentMinimum
open OriginalActiveClassKernel
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- On an original source-universe seed, the ORIGINAL computed class consists
exactly of source-universe candidates with the same ORIGINAL least-code key.
This is a native correspondence theorem, not an internal derivation. -/
theorem classNumberCharacterization (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty)
    (hclosed : SubtypeClosed (fun tau => tau ∈ S))
    (q : Packed (Fin n) arity Gamma) (hq : InUniverse symbols S q.2) (candidate : Nat) :
    NumberedRepresentativePrimrec.classNumberTest symbols S q candidate = true ↔
      sourceValidityValue n arity symbols S Gamma candidate = 1 ∧
      targetValidityValue n arity Gamma candidate = 1 ∧
      representativeCode symbols S q = targetRepresentativeValue n arity symbols S Gamma candidate := by
  cases hd : decodePackedNumber n arity Gamma candidate with
  | none =>
    simp [NumberedRepresentativePrimrec.classNumberTest,sourceValidityValue,
      rawCarrierTest,decodeUniverse,targetValidityValue,targetRepresentativeValue,hd]
  | some r =>
    cases hu : universeTest symbols S r.2 with
    | false =>
      have hn : r ∉ primaryClass symbols S q := by
        intro hm
        have hp := (NumberedFinitePrimaryClassProof.exactPrimaryClass
          (Fin n) inferInstance arity symbols S hclosed Gamma q hq r).mp hm
        have hr := (NumberedWindowEquivalenceProof.actualPrimaryConfinement
          (Fin n) arity symbols S Gamma q r hp).mp hq
        have hb := (NumberedNumericCarrierProof.universeTestCorrect
          (Fin n) inferInstance arity symbols S Gamma r.1 r.2).mpr hr
        rw [hu] at hb
        contradiction
      simp [NumberedRepresentativePrimrec.classNumberTest,primaryTest,sourceValidityValue,
        rawCarrierTest,decodeUniverse,targetValidityValue,targetRepresentativeValue,hd,hu,hn]
    | true =>
      have hr : InUniverse symbols S r.2 :=
        (NumberedNumericCarrierProof.universeTestCorrect
          (Fin n) inferInstance arity symbols S Gamma r.1 r.2).mp hu
      have hm : r ∈ primaryClass symbols S q ↔
          representativeCode symbols S q = representativeCode symbols S r :=
        (NumberedFinitePrimaryClassProof.exactPrimaryClass
          (Fin n) inferInstance arity symbols S hclosed Gamma q hq r).trans
          (NumberedLeastCodeRepresentativeProof.representativeEquality
            n arity symbols S hclosed Gamma q r hq hr).symm
      simpa [NumberedRepresentativePrimrec.classNumberTest,primaryTest,sourceValidityValue,
        rawCarrierTest,decodeUniverse,targetValidityValue,targetRepresentativeValue,hd,hu] using hm

abbrev rawClassValue (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (seed candidate : Nat) : Nat :=
  ((NumberedUniformPackedDecoding.rawPackedDecode n arity Gamma seed).any
    (fun q => ContextUniformPrimary.classNumberTest arity symbols S Gamma q candidate)).toNat

theorem rawClassCharacterization (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty)
    (hclosed : SubtypeClosed (fun tau => tau ∈ S)) (seed candidate : Nat)
    (hs : sourceValidityValue n arity symbols S Gamma seed = 1) :
    rawClassValue n arity symbols S Gamma seed candidate = 1 ↔
      sourceValidityValue n arity symbols S Gamma candidate = 1 ∧
      targetValidityValue n arity Gamma candidate = 1 ∧
      targetRepresentativeValue n arity symbols S Gamma seed =
        targetRepresentativeValue n arity symbols S Gamma candidate := by
  cases hd : decodeUniverse n arity symbols S Gamma seed with
  | none => simp [sourceValidityValue,rawCarrierTest,hd] at hs
  | some q =>
    have hp := (Option.filter_eq_some_iff.mp hd).1
    have hq := (NumberedNumericCarrierProof.numericUniverseDecode
      n arity symbols S Gamma seed q).mp hd
    have hc := classNumberCharacterization n arity symbols S Gamma hclosed q hq.2 candidate
    unfold rawClassValue
    rw [NumberedUniformPackedDecodingProof.rawPackedCalibration,hp]
    simp only [Option.map_some,Option.any_some]
    rw [ContextUniformPrimaryCalibrationProof.classNumberTestCalibration]
    simpa [targetRepresentativeValue,hp] using hc

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalActiveClassKernelCalibrationSupportProof
