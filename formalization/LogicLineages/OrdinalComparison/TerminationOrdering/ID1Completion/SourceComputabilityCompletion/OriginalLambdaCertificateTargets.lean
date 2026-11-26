module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse
open NumberedLeastCodeRepresentative NumberedTypedFocus NumberedStepCertificate NumberedNumericStep
open OriginalLambdaCertificate

/-- The original typed checker beneath a lambda is exactly its child checker,
including rejection. Replacement and root selector remain literally equal. -/
def ActualTypedLambdaCertificateLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (body body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (child : StepCertificate),
  stepTest n arity symbols S Gamma table (.lam body) (.lam body')
      (liftCertificate child) =
    stepTest n arity symbols S (sigma :: Gamma) table body body' child

/-- An empty path must invoke an actual root rule. For a lambda the only
accepted original root rule is the same-type bottom rule. -/
def ActualTypedLambdaCertificateRootBottom : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (target : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (replacement root : Nat),
  stepTest n arity symbols S Gamma table (.lam body) target
      ⟨[],replacement,root⟩ = true →
    target = .bottom (.arrow sigma tau)

/-- Every nonempty original focus path at a lambda must start with lam.
No semantic reduction theorem can bypass this checker-level rejection. -/
def ActualLambdaCertificateOtherPositionRejected : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (position : Position) (rest : List Position),
  position ≠ .lam → focus (position :: rest) (.lam body) = none

/-- Invert this specific successful typed certificate. The recovered child
uses its exact path suffix, replacement and root, not a completeness witness. -/
def ActualTypedLambdaCertificateNonbottomInversion : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
    (target : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (certificate : StepCertificate),
  target ≠ .bottom (.arrow sigma tau) →
  stepTest n arity symbols S Gamma table (.lam body) target certificate = true →
  ∃ (body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau) (rest : List Position),
    target = .lam body' ∧ certificate.path = .lam :: rest ∧
      stepTest n arity symbols S (sigma :: Gamma) table body body'
        ⟨rest,certificate.replacement,certificate.root⟩ = true

/-- Literal numeric coding facts. The right pair is preserved on ALL raw
inputs. On a decoded lambda path, stripping preserves both fields and recovers
the exact child; prefixing it restores the original supplied number. -/
def ActualLambdaCertificateStrip : Prop :=
  (∀ certificate : Nat,
    (Nat.unpair (stripStep certificate)).2 = (Nat.unpair certificate).2) ∧
  (∀ child : StepCertificate,
    liftStep (stepCertificateNumber child) = stepCertificateNumber (liftCertificate child)) ∧
  (∀ (certificate : Nat) (decoded : StepCertificate) (rest : List Position),
    decodeStepCertificate certificate = some decoded → decoded.path = .lam :: rest →
    stripStep certificate = stepCertificateNumber ⟨rest,decoded.replacement,decoded.root⟩ ∧
      decodeStepCertificate (stripStep certificate) =
        some ⟨rest,decoded.replacement,decoded.root⟩ ∧
      certificate = liftStep (stripStep certificate))

/-- SAME-witness native numeric inversion for the original checker. Its own
successful source decoding supplies body membership, so neither subtype closure
nor an extra type-window premise is assumed. The exact accepted raw certificate
decodes with a lam prefix; the literal strip above, with unchanged replacement
and root, is accepted at sigma::Gamma. This does not assert an internal-calculus
rule, a quotient/canonical lambda law, substitution, or lambda computability. -/
def ActualNumericLambdaCertificateNonbottomInversion : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (body : AuxTerm (Fin n) arity (sigma :: Gamma) tau) (target certificate : Nat),
  target ≠ packedNumber (⟨.arrow sigma tau,.bottom (.arrow sigma tau)⟩ :
    Packed (Fin n) arity Gamma) →
  numericStepTest n arity symbols S Gamma table
    (packedNumber (⟨.arrow sigma tau,.lam body⟩ : Packed (Fin n) arity Gamma))
    target certificate = true →
  InUniverse symbols S body ∧
    ∃ (body' : AuxTerm (Fin n) arity (sigma :: Gamma) tau)
      (decoded : StepCertificate) (rest : List Position),
      decodeStepCertificate certificate = some decoded ∧
      decoded.path = .lam :: rest ∧
      target = packedNumber (⟨.arrow sigma tau,.lam body'⟩ : Packed (Fin n) arity Gamma) ∧
      stripStep certificate = stepCertificateNumber ⟨rest,decoded.replacement,decoded.root⟩ ∧
      decodeStepCertificate (stripStep certificate) =
        some ⟨rest,decoded.replacement,decoded.root⟩ ∧
      certificate = liftStep (stripStep certificate) ∧
      stepTest n arity symbols S (sigma :: Gamma) table body body'
        ⟨rest,decoded.replacement,decoded.root⟩ = true ∧
      numericStepTest n arity symbols S (sigma :: Gamma) table
        (packedNumber (⟨tau,body⟩ : Packed (Fin n) arity (sigma :: Gamma)))
        (packedNumber (⟨tau,body'⟩ : Packed (Fin n) arity (sigma :: Gamma)))
        (stripStep certificate) = true

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaCertificateTargets
