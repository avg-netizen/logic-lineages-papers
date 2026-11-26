module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepRunProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathRunTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceBranchProof
open InternalAcceptanceNormalizationProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open OriginalTransparentMixedPathDefinitions
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def RunForward : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (source : Program 2)
    (xs ys : Fin 4 → OTerm alpha) (code head tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hr : Nonempty (Derivation body Delta (programGraph (run source) out xs))),
    Nonempty (Derivation body Delta (programGraph (run source) out ys))

def RunBackward : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (source : Program 2)
    (xs ys : Fin 4 → OTerm alpha) (code head tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hr : Nonempty (Derivation body Delta (programGraph (run source) out ys))),
    Nonempty (Derivation body Delta (programGraph (run source) out xs))

def RefinedForward : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (source : Program 2) (oldStep : Program 4)
    (xs ys : Fin 4 → OTerm alpha) (code head tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hout : Nonempty (Derivation body Delta (programGraph (refined source oldStep) out xs))),
    Nonempty (Derivation body Delta (programGraph (refined source oldStep) out ys))

def RefinedBackward : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha)) (source : Program 2) (oldStep : Program 4)
    (xs ys : Fin 4 → OTerm alpha) (code head tail state next out : OTerm alpha)
    (hp : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path code xs)))
    (ht : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.path tail ys)))
    (hl : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live state xs)))
    (hn : Nonempty (Derivation body Delta (programGraph OriginalHereditaryLambda.live next ys)))
    (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode code head tail)))
    (hstep : Nonempty (Derivation body Delta (graph1 (transition source) next state)))
    (hout : Nonempty (Derivation body Delta (programGraph (refined source oldStep) out ys))),
    Nonempty (Derivation body Delta (programGraph (refined source oldStep) out xs))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathRunTargets
