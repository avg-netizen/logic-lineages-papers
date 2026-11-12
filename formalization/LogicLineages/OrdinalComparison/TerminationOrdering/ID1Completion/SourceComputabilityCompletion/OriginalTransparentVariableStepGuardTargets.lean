module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNeutralLeafDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Both actual neutral and constructor guards at the unchanged four inputs.
This is a supporting contract, not final positive-certificate acceptance.
No guard acceptance or opaque oldStep fact occurs among its premises. -/
def ActualOriginalVariableBottomGuards : Prop :=
  ∀ (endpoint : Program 6) (window : Program 1) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (s t cert parameter typ : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 OriginalLambdaConstructor.tag z s ⊓
      (graph1 InternalUnpair.left typ s ⊓ graph1 BottomRepresentative.bottomCode t typ)).imp
      (graph4 (OriginalNeutralLeaf.leafGuard endpoint window) (suc z) s t cert parameter ⊓
        graph4 (InternalAcceptance.conjunction
          (UniformCertificateCompletion.PositiveGuard.nonBottomGuard BottomRepresentative.bottomTest)
          OriginalConstructorLeaf.variableGuard) (suc z) s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentVariableStepGuardTargets
