module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedTypedFocus
open NumberedNumericDecoding NumberedNumericCarrier NumberedStepCertificate
open NumberedNumericStep NumberedNumericStepPrimrec ApplicationCertificateLift

/-- Literal position 2 is appFunction in the original numbering. The suffix
may decode to none because it contains an invalid position code. -/
def ActualPathDecoderLift : Prop :=
  ∀ path : Nat,
    decodePath (1 + Nat.pair 2 path) =
      (decodePath path).map (fun positions => .appFunction :: positions)

/-- No successful-decoding hypothesis: malformed path positions stay rejected. -/
def ActualCertificateDecoderLift : Prop :=
  ∀ certificate : Nat,
    decodeStepCertificate (liftStep certificate) =
      (decodeStepCertificate certificate).map liftCertificate

/-- No typing assumptions on the raw Code inputs; original focus/replacement
and root-selector tests are unchanged. -/
def ActualRawCodeIdentity : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (sigma tau : Ty) (q r a : Code (Fin n)) (certificate : StepCertificate),
    stepCodeTest n arity symbols S Gamma table tau
      (.app sigma q a) (.app sigma r a) (liftCertificate certificate) =
    stepCodeTest n arity symbols S Gamma table (.arrow sigma tau) q r certificate

/-- The literal application source guard, with no hidden closure hypothesis. -/
def ActualSourceUniverseDecomposition : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (sigma tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma),
    InUniverse symbols S (.app q a) ↔
      tau ∈ S ∧ InUniverse symbols S q ∧ InUniverse symbols S a

/-- Equality of the original Boolean checker on every natural certificate.
The target r is typed but is not given an additional universe premise. -/
def ActualTypedNumericIdentity : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (sigma tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (certificate : Nat),
    InUniverse symbols S q → InUniverse symbols S a → tau ∈ S →
    numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma))
      (packedNumber (⟨tau,.app r a⟩ : Packed (Fin n) arity Gamma))
      (liftStep certificate) =
    numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
      (packedNumber (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma)) certificate

/-- Arbitrary natural endpoints with exactly the original decoder guards.
Only source and argument use decodeUniverse; target uses decodePackedNumber. -/
def ActualRawEndpointIdentity : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n))
    (S Gamma : List Ty) (table : Fin n → Fin n → Bool)
    (sigma tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma)
    (source target argument certificate : Nat),
    decodeUniverse n arity symbols S Gamma source = some ⟨.arrow sigma tau,q⟩ →
    decodePackedNumber n arity Gamma target = some ⟨.arrow sigma tau,r⟩ →
    decodeUniverse n arity symbols S Gamma argument = some ⟨sigma,a⟩ →
    tau ∈ S →
    numericStepTest n arity symbols S Gamma table
      (rawApplication (typeNumber sigma) (typeNumber tau) source argument)
      (rawApplication (typeNumber sigma) (typeNumber tau) target argument)
      (liftStep certificate) =
    numericStepTest n arity symbols S Gamma table source target certificate

/-- The original subtype-closed window supplies the explicit result-type guard;
this still states equality for rejected as well as accepted certificates. -/
def ActualSubtypeClosedNumericIdentity : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) →
  ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (certificate : Nat),
    InUniverse symbols S q → InUniverse symbols S a →
    numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma))
      (packedNumber (⟨tau,.app r a⟩ : Packed (Fin n) arity Gamma))
      (liftStep certificate) =
    numericStepTest n arity symbols S Gamma table
      (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
      (packedNumber (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma)) certificate

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationStepGuardTargets
