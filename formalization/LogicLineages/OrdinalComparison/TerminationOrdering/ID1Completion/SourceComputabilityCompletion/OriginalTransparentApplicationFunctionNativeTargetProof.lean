module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackDecoderProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTargetProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open InternalApplicationValidityStack InternalOriginalStepGuard
open InternalApplicationValidityStackDecoderProof

/-- A malformed function payload cannot become a typed application by appending
an argument. This is original target decoding, not universe membership. -/
theorem malformedApplication (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
 (sigma tau : Ty) (fp ap : Nat)
 (hf : decodePackedNumber n arity Gamma (Nat.pair (typeNumber (.arrow sigma tau)) fp) = none) :
 decodePackedNumber n arity Gamma
   (Nat.pair (typeNumber tau) (Nat.pair 2 (Nat.pair (typeNumber sigma) (Nat.pair fp ap)))) = none := by
 cases hd : decodePackedNumber n arity Gamma
   (Nat.pair (typeNumber tau) (Nat.pair 2 (Nat.pair (typeNumber sigma) (Nat.pair fp ap)))) with
 | none => rfl
 | some q =>
   have hv : targetValidityValue n arity Gamma
     (Nat.pair (typeNumber tau) (Nat.pair 2 (Nat.pair (typeNumber sigma) (Nat.pair fp ap)))) = 1 := by
     simp [targetValidityValue,hd]
   have hw := (targetWitness n arity Gamma tau _).mp hv
   have hh := (applicationWitness n arity Gamma sigma tau fp ap).mp hw
   have hk := (targetWitness n arity Gamma (.arrow sigma tau) fp).mpr hh.1
   simp [targetValidityValue,hf] at hk

/-- Successful arbitrary target-function decoding at the literal arrow code
retains that exact arrow type, including non-universe targets. -/
theorem functionType (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
 (sigma tau : Ty) (fp : Nat) (q : Packed (Fin n) arity Gamma)
 (hq : decodePackedNumber n arity Gamma (Nat.pair (typeNumber (.arrow sigma tau)) fp) = some q) :
 q.1 = .arrow sigma tau := by
 have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma _ q hq
 have ht := (Nat.pair_eq_pair.mp he).1
 exact NumberedLeastCodeRepresentativeSupportProof.typeNumberInjective ht

/-- Arbitrary target payload, including rejected decodes. The only universe
premises concern the actual original source function and unchanged argument. -/
theorem allTargetIdentity (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
 (S Gamma : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty)
 (q : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
 (a : AuxTerm (Fin n) arity Gamma sigma) (targetPayload certificate : Nat)
 (hq : NumberedFiniteUniverse.InUniverse symbols S q)
 (ha : NumberedFiniteUniverse.InUniverse symbols S a) (ht : tau ∈ S) :
 NumberedNumericStep.numericStepTest n arity symbols S Gamma table
   (packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma))
   (Nat.pair (typeNumber tau) (Nat.pair 2 (Nat.pair (typeNumber sigma)
      (Nat.pair targetPayload (codeNumber (termCode a))))))
   (ApplicationCertificateLift.liftStep certificate) =
 NumberedNumericStep.numericStepTest n arity symbols S Gamma table
   (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
   (Nat.pair (typeNumber (.arrow sigma tau)) targetPayload) certificate := by
 cases hd : decodePackedNumber n arity Gamma
   (Nat.pair (typeNumber (.arrow sigma tau)) targetPayload) with
 | none =>
   have had := malformedApplication n arity Gamma sigma tau targetPayload (codeNumber (termCode a)) hd
   simp [NumberedNumericStep.numericStepTest,hd,had]
 | some r =>
   have hr := functionType n arity Gamma sigma tau targetPayload r hd
   rcases r with ⟨rt,r⟩
   dsimp only at hr
   subst rt
   have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma _ ⟨.arrow sigma tau,r⟩ hd
   have hp : codeNumber (termCode r) = targetPayload := (Nat.pair_eq_pair.mp he).2
   have hh := ApplicationStepGuardProof.actualTypedNumericIdentity n arity symbols S Gamma table
     sigma tau q r a certificate hq ha ht
   simpa only [packedNumber,termCode,codeNumber,hp] using hh

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTargetProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentApplicationFunctionNativeTargetProof
