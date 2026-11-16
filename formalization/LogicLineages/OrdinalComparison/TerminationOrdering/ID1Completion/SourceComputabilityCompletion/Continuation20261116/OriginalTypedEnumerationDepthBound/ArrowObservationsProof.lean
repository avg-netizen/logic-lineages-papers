module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalScalarProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArrowObservationsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalControlGraphSupportProof (projectionValue emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open OriginalTypedDecoder OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def queries : Fin 2 → Program 1 := ![headOf (.projection 0),tailOf (.projection 0)]

theorem cases (code : OTerm alpha) (psi : Formula alpha)
    (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (domain codomain : OTerm beta),
      (∀ q ∈ Delta, q.relabel j ∈ Theta) →
      Nonempty (Derivation body Theta (StepArrowFields (code.relabel j) domain codomain)) →
      Nonempty (Derivation body Theta (psi.relabel j))) :
    Nonempty (Derivation body Delta psi) := by
  apply OriginalLambdaConstructorGraphSyntaxProof.queryCases queries (Fin.cons code Fin.elim0) psi
  intro beta j ys Theta hj hq
  simp only [consTermRename,emptyRename] at hq
  apply next beta j Theta (ys 0) (ys 1) hj
  exact OriginalTypedDecoderInternalScalarProof.arrowFields (.projection 0) (code.relabel j) (ys 0) (ys 1)
    ![code.relabel j] (projectionValue 0 ![code.relabel j]) (hq 0) (hq 1)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArrowObservationsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalTypedEnumerationDepthBound.ArrowObservationsProof
