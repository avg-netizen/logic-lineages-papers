module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathNilTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (z)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Any result, any source Program and any checker. Only the actual original
empty certificate path is supplied. No source validity or run success oracle. -/
def ActualNilNormalization : Prop :=
  ∀ (source : Program 2) (oldStep : Program 4) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (out s t cert parameter : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 InternalUnpair.left z cert).imp
      ((graph4 (OriginalTransparentMixedPathDefinitions.refined source oldStep) out s t cert parameter).iff
        (graph4 oldStep out s t cert parameter))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentMixedPathNilTargets
