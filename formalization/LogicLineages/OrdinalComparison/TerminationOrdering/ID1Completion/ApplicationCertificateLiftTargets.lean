module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedStepCertificate NumberedNumericStep ApplicationCertificateLift
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualTypedLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (c : StepCertificate),
  stepTest n arity symbols S Gamma table (.app q a) (.app r a) (liftCertificate c) =
    stepTest n arity symbols S Gamma table q r c

def ActualApplicationEncoding : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (sigma tau : Ty)
    (q : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma),
  rawApplication (typeNumber sigma) (typeNumber tau)
    (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
    (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)) =
  packedNumber (⟨tau,.app q a⟩ : Packed (Fin n) arity Gamma)

def ActualStepEncoding : Prop :=
  ∀ c : StepCertificate, liftStep (stepCertificateNumber c) =
    stepCertificateNumber (liftCertificate c)

def ActualPrimitive : Prop :=
  Primrec applicationValue ∧ Primrec liftStep ∧ Primrec stepValue

def ActualProgramWitnesses : Prop :=
  ∃ (application : Program 4) (step : Program 1),
    (∀ v, evaluate application v = applicationValue v) ∧
    (∀ v, evaluate step v = stepValue v)

/-- This preserves the specific supplied original certificate, rather than
using completeness to select some unrelated successful certificate. -/
def ActualOriginalNumericLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
  SubtypeClosed (fun t => t ∈ S) →
  ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (q r : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (certificate : Nat),
  InUniverse symbols S q → InUniverse symbols S a →
  numericStepTest n arity symbols S Gamma table
    (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
    (packedNumber (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma)) certificate = true →
  numericStepTest n arity symbols S Gamma table
    (rawApplication (typeNumber sigma) (typeNumber tau)
      (packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma))
      (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)))
    (rawApplication (typeNumber sigma) (typeNumber tau)
      (packedNumber (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma))
      (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)))
    (liftStep certificate) = true

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftTargets
