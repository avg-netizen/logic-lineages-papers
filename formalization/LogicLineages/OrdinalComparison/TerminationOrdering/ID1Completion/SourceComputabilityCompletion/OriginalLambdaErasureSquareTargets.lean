module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaErasureSquareDefinitions

/-- Coordinate-exposed packed lambda/context square only. No certificate,
canonical equality, transformed-rank strictness, or I/C endpoint is asserted. -/
def ActualOriginalLambdaErasureCoordinateSquare : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s out child childOut domain codomain arrow raw childRaw inner childRawOut innerOut rawOut
      erasedType cutoff gamma extended childGamma childExtended : OTerm alpha),
  Nonempty (Derivation body Delta
    ((Premises s out child childOut domain codomain arrow raw childRaw inner childRawOut innerOut rawOut
      erasedType cutoff gamma extended childGamma childExtended).imp
      (Result out child childOut domain codomain erasedType cutoff childGamma childExtended)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaErasureSquareTargets
