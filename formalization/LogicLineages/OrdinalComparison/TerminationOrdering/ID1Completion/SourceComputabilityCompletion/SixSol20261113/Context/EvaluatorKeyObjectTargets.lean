module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorKeyPut
/-- Actual Object-wrapper equality on admitted original evaluator fibres at
one actual encoded Gamma. Pair and parameter graphs preserve bookkeeping;
no wrapper/fold output equality, fixedness or cancellation is supplied. -/
def ActualObjectEquality : Prop :=
 ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
 (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
 (leftObject rightObject leftRaw rightRaw leftOut rightOut context gamma parameter : OTerm alpha),
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing leftObject gamma leftRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rightObject gamma rightRaw)) →
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)) →
 Nonempty (Derivation body Delta (Domain p H G W leftRaw parameter)) →
 Nonempty (Derivation body Delta (Domain p H G W rightRaw parameter)) →
 Nonempty (Derivation body Delta (Same p H G W leftRaw rightRaw parameter)) →
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) leftOut context leftObject)) →
 Nonempty (Derivation body Delta (graph2 (EvaluatorKeyObjectDefinitions.object p H G W P) rightOut context rightObject)) →
 Nonempty (Derivation body Delta (equal leftOut rightOut))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorKeyObjectTargets
