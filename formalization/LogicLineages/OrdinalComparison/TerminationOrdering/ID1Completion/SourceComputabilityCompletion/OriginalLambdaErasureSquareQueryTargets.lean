module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors

/-- Internally construct the four relevant witnesses and discharge all raw
coordinates. The continuation is ordinary binder-safe existential elimination,
NOT an assumed child certificate or erasure law. packedLambda takes the actual
untyped body payload; no discarded outer body type is silently inferred. -/
def ActualOriginalLambdaErasureSquareQuery : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s out domain codomain childRaw erasedType cutoff gamma extended : OTerm alpha)
    (psi : Formula alpha),
  Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.packedLambda s domain codomain childRaw)) →
  Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw out erasedType cutoff s)) →
  Nonempty (Derivation body Delta (OriginalContextInsertion.Insert erasedType cutoff gamma extended)) →
  (∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
      (child childOut childGamma childExtended : OTerm beta),
    (∀ p ∈ Delta, p.relabel j ∈ Theta) →
    Nonempty (Derivation body Theta
      (graph2 OriginalLambdaConstructor.bodyCode child (codomain.relabel j) (s.relabel j) ⊓
        OriginalLambdaErasureSquareDefinitions.Result (out.relabel j) child childOut
          (domain.relabel j) (codomain.relabel j) (erasedType.relabel j) (cutoff.relabel j)
          childGamma childExtended)) →
    Nonempty (Derivation body Theta (psi.relabel j))) →
  Nonempty (Derivation body Delta psi)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareQueryTargets
