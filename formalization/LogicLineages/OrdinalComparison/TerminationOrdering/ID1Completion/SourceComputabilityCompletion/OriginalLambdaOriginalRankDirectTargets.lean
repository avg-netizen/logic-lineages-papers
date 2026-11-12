module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDirectTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalLambdaOriginalRankDefinitions
/-- Object-level child dichotomy is sufficient. Unlike the earlier fixed-context
CPS supplier, this premise is directly furnished by internal path induction. -/
def ActualDirectCongruence : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter childS childT childParam d e context gamma extended
      oldS oldT oldChildS oldChildT before after : OTerm alpha),
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentLambdaStep.refined source oldStep)
  Nonempty (Derivation body Delta
    (OriginalLambdaErasureSquareDichotomyDefinitions.Frame source
      s t parameter childS childT childParam d e context gamma extended)) →
  Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldS d e oldChildS)) →
  Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldT d e oldChildT)) →
  Nonempty (Derivation body Delta (Result leaf childS childT childParam oldChildS oldChildT before after)) →
  Nonempty (Derivation body Delta (Result leaf s t parameter oldS oldT before after))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaOriginalRankDirectTargets
