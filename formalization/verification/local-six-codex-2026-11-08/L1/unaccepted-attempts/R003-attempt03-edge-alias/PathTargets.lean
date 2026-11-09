module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open InternalOriginalUniformContextMembership (normalizeData)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The original parameterized list-code induction, now discharged for the
concrete uniform quotient edge and literal dispatched actualJ vertex.
Gamma is symbolic; source/target, original certificate and all three supplied
outputs are arbitrary. No local edge law or path invariant is assumed. -/
def ActualOriginalUniformPositiveApplicationPathLift : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (base : Data),
  InternalOriginalUniformDescentSelection.Calibrated n arity base →
  ∀ (window : Program 1), Path.windowCalibrated n window →
  ∀ (symbols : List (Fin n)) (S : List Ty) (table : Fin n → Fin n → Bool),
  SubtypeClosed (fun typ => typ ∈ S) →
  ∀ (oldStep : Program 4) (oldVertex : Program 5) (body : Positive (Fin 1))
    (α : Type) (Delta : List (Formula α)) (sigma tau : Ty)
    (parameter gammaCode x y argument certificate out other mapped : OTerm α),
  Nonempty (Derivation body Delta
    ((Path.positivePremises (OrdinaryArithmeticQuotient.contextCode symbols S table)
      (normalizeData base) oldStep window oldVertex sigma tau
      parameter gammaCode x y argument certificate out other mapped).imp
      (InternalParameterizedPathChecker.positiveGraph (edgeChecker (normalizeData base) oldStep)
        out other mapped parameter)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.UniformCertificateCompletion.PathTargets
