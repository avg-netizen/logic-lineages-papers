module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedStepCertificate NumberedNumericStep
open NumberedDirectCertificate InternalOriginalUniformParameterLeaves OriginalBetaResult
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The literal pair has exactly the existing StepCertificate numbering and
decodes to the same empty path, raw replacement and beta-selector number. -/
def ActualOriginalBetaCertificateCoding : Prop :=
  ∀ replacement : Nat,
    rootCertificate replacement =
      stepCertificateNumber ⟨[],replacement,Nat.pair 2 0⟩ ∧
    decodeStepCertificate (rootCertificate replacement) =
      some ⟨[],replacement,Nat.pair 2 0⟩

/-- Exact Boolean calibration of this ORIGINAL numeric certificate, including
all rejected sources, targets and replacements. Only the actual source has
the source-universe guard. The target and replacement must both be the SAME
literal capture-avoiding contractum. No subtype-closure, target-universe,
computability or additional window hypothesis is supplied. -/
def ActualOriginalNumericBetaCertificate : Prop := by
  classical
  exact ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (a : AuxTerm (Fin n) arity Gamma sigma) (target replacement : Nat),
    numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma))
      target (rootCertificate replacement) =
        decide (InUniverse symbols S (.app (.lam body) a) ∧
          target = packedNumber
            (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma) ∧
          replacement = packedNumber
            (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma))

/-- The raw computation agrees on EVERY natural with the ORIGINAL dependent
typed packed decoder followed by the ORIGINAL direct beta rule, including
typing failure and non-beta shapes. Success is successor of packedNumber. -/
def ActualOriginalBetaRawCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (source : Nat),
    rawResult n arity Gamma source =
      (((decodePackedNumber n arity Gamma source).bind
        (directTarget arity Gamma .beta)).map (fun result =>
          Nat.succ (packedNumber result))).getD 0

/-- ALL original parameter vectors, including context-decoding failure.
This compares the candidate raw arithmetic function against the unchanged
native typed beta semantics, not against a successful-decode-only wrapper. -/
def ActualOriginalBetaUniformCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 2),
    resultValue n arity v =
      decodedValue n (fun _ obj =>
        (((decodePackedNumber n arity obj.1 obj.2).bind
          (directTarget arity obj.1 .beta)).map (fun result =>
            Nat.succ (packedNumber result))).getD 0) (v.get 0) (v.get 1)

/-- Primitive recursion is established jointly in the original raw source
and unchanged parameter. Neither a PR premise nor a frozen Gamma is allowed. -/
def ActualOriginalBetaResultPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), Primrec (resultValue n arity)

/-- ONE binary Program is selected after the ranked signature and BEFORE
symbols, S, Gamma and table. It is calibrated on every input vector and every
raw source slice, and its typed beta specialization returns precisely the
original packed capture-avoiding substitution result. No source membership,
type-window closure, computability or internal reflection premise is added.
This does not select or alter any final source-presentation Package. -/
def ActualOriginalBetaResultProgram : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
    ∃ B : Program 2,
      OriginalBetaResult.Calibrated n arity B ∧
      (∀ (symbols : List (Fin n)) (S Gamma : List Ty)
          (table : Fin n → Fin n → Bool) (source : Nat),
        evaluate B (List.Vector.ofFn ![source,parameterCode symbols S Gamma table]) =
          rawResult n arity Gamma source) ∧
      (∀ (symbols : List (Fin n)) (S Gamma : List Ty)
          (table : Fin n → Fin n → Bool) (sigma tau : Ty)
          (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
          (a : AuxTerm (Fin n) arity Gamma sigma),
        evaluate B (List.Vector.ofFn ![
          packedNumber (⟨tau,.app (.lam body) a⟩ : Packed (Fin n) arity Gamma),
          parameterCode symbols S Gamma table]) =
            Nat.succ (packedNumber
              (⟨tau,substitute body (singleSubstitution a)⟩ : Packed (Fin n) arity Gamma)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalBetaResultTargets
