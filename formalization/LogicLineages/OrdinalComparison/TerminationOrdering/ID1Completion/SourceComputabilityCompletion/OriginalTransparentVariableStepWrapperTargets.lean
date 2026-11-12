module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryLambdaGlobalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepWrapperTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Construct the entire unchanged two-layer wrapper, including hereditary
nil-path acceptance. Raw source membership is explicit; extracting it from
final typedness and assembling the full positive checker remain separate.
No supplied spine/neutral/constructor/hereditary guard acceptance occurs. -/
def ActualOriginalTransparentVariableClosedLeaf : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (endpoint : Program 6) (window : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter typ : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 source (suc z) s parameter ⊓
      (graph1 OriginalLambdaConstructor.tag z s ⊓
        (graph1 InternalUnpair.left typ s ⊓
          (graph1 BottomRepresentative.bottomCode t typ ⊓
            graph1 OriginalTransparentVariableStep.certificateCode cert s)))).imp
      (graph4 (OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
        (OriginalTransparentVariableStep.refined source oldStep)) (suc z) s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepWrapperTargets
