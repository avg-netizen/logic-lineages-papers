module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTransparentMixedDirectBottom (source leaf)
open OriginalExistentialRankResultDefinitions (Result)
/-- Local direct object-level child dichotomy only; no erased-source coherence or full-chain assertion. -/
def ActualLambda : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t parameter childS childT childParam d e context gamma extended oldS oldT oldChildS oldChildT : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalLambdaErasureSquareDichotomyDefinitions.Frame (source H G M W)
  s t parameter childS childT childParam d e context gamma extended)) →
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldS d e oldChildS)) →
 Nonempty (Derivation body Delta (graph3 OriginalLambdaConstructor.constructor oldT d e oldChildT)) →
 Nonempty (Derivation body Delta (Result (leaf H G M W oldStep) childS childT childParam oldChildS oldChildT)) →
 Nonempty (Derivation body Delta (Result (leaf H G M W oldStep) s t parameter oldS oldT))
/-- The SAME original argument and SAME transformed argument are each explicit. Rank witnesses concern only ORIGINAL endpoints. -/
def ActualApplication : Prop := ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (s t parameter childS childT arg d e arrow oldS oldT oldChildS oldChildT oldArg : OTerm alpha),
 Nonempty (Derivation body Delta (OriginalMixedExistentialCongruenceDefinitions.ApplicationFrame (source H G M W)
  s t parameter childS childT arg d e arrow)) →
 Nonempty (Derivation body Delta (graph4 application oldS d e oldChildS oldArg)) →
 Nonempty (Derivation body Delta (graph4 application oldT d e oldChildT oldArg)) →
 Nonempty (Derivation body Delta (Result (leaf H G M W oldStep) childS childT parameter oldChildS oldChildT)) →
 Nonempty (Derivation body Delta (Result (leaf H G M W oldStep) s t parameter oldS oldT))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalMixedExistentialCongruenceTargets
