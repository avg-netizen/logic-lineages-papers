module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedNumericStep NumberedNumericQuotientEdge ApplicationCertificateLift ApplicationCertificateLiftEdge
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualEncoding : Prop :=
  ∀ domain codomain argument source target step : Nat,
    liftEdge domain codomain argument (edgeCertificateNumber source target step) =
      edgeCertificateNumber (rawApplication domain codomain source argument)
        (rawApplication domain codomain target argument) (liftStep step)

def ActualPrimitive : Prop := Primrec edgeValue

def ActualProgramWitness : Prop :=
  ∃ p : Program 4, ∀ v, evaluate p v = edgeValue v

/-- The supplied edge certificate itself presents an original step between
arrow-typed raw witnesses, with exactly its own source/target/step fields. -/
def ActualTypedEdgePresentation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) →
  ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (y certificate : Nat),
    InUniverse symbols S f →
    numericEdgeTest n arity symbols S Gamma table
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩) y certificate = true →
    ∃ q r : AuxTerm (Fin n) arity Gamma (.arrow sigma tau),
      InUniverse symbols S q ∧ InUniverse symbols S r ∧
      packedNumber (⟨.arrow sigma tau,q⟩ : Packed (Fin n) arity Gamma) = sourceOf certificate ∧
      packedNumber (⟨.arrow sigma tau,r⟩ : Packed (Fin n) arity Gamma) = targetOf certificate ∧
      representativeCode symbols S ⟨.arrow sigma tau,q⟩ =
        representativeCode symbols S ⟨.arrow sigma tau,f⟩ ∧
      representativeCode symbols S ⟨.arrow sigma tau,r⟩ = y ∧
      numericStepTest n arity symbols S Gamma table
        (sourceOf certificate) (targetOf certificate) (stepOf certificate) = true

/-- Preserve the exact explicit transformed edge between the canonical
application endpoints, not merely existential edge or path membership. -/
def ActualOriginalEdgeLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) →
  ∀ (Gamma : List Ty) (table : Fin n → Fin n → Bool) (sigma tau : Ty)
    (f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma) (certificate : Nat),
    InUniverse symbols S f → InUniverse symbols S g → InUniverse symbols S a →
    numericEdgeTest n arity symbols S Gamma table
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩)
      (representativeCode symbols S ⟨.arrow sigma tau,g⟩) certificate = true →
    numericEdgeTest n arity symbols S Gamma table
      (representativeCode symbols S ⟨tau,.app f a⟩)
      (representativeCode symbols S ⟨tau,.app g a⟩)
      (liftEdge (typeNumber sigma) (typeNumber tau)
        (packedNumber (⟨sigma,a⟩ : Packed (Fin n) arity Gamma)) certificate) = true

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationCertificateLiftEdgeTargets
