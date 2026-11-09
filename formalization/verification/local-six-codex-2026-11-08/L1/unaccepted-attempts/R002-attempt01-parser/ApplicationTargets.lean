module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Concrete local application-edge lifting on the SAME original checker.
Codomain membership, target typing, raw selector witnesses and output
representative facts are derived internally. Runtime Gamma is symbolic. -/
def ActualOriginalUniformApplicationEdgeLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (oldStep : Program 4) (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (x y a certificate out other lifted parameter gammaCode : OTerm α),
  Nonempty (Derivation body Delta
    ((Application.liftPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (normalizeData base) oldStep sigma tau x y a certificate out other lifted parameter gammaCode).imp
      (edgeAccepted (normalizeData base) oldStep out other lifted parameter)))

/-- Both SUPPLIED actualJ outputs have the original codomain type. The
second input is typed by the unchanged edge, not an added hypothesis.
Original contextual membership is discharged from the same normalized base. -/
def ActualOriginalUniformApplicationEdgeTypedOutputs : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (oldStep : Program 4) (body : Positive (Fin 1)) (α : Type) (Delta : List (Formula α))
    (sigma tau : Ty) (x y a certificate out other lifted parameter gammaCode : OTerm α),
  Nonempty (Derivation body Delta
    ((Application.liftPremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (normalizeData base) oldStep sigma tau x y a certificate out other lifted parameter gammaCode).imp
      (Application.typedOutputs (normalizeData base) tau out other parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.ApplicationTargets
