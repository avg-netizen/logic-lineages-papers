module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors OriginalTransparentDirectBottomDichotomy
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Source validity and literal same-type bottom suffice: equality or an
internally constructed exact original certificate in the SAME closed leaf.
No nonbottom, certificate, or guard-acceptance premise is supplied. -/
def ActualConcreteDirectBottomDichotomy : Prop :=
  ∀ (H G : Program 1) (M W : Program 2) (oldStep : Program 4)
    (endpoint : Program 6) (window : Program 1) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (s t parameter typ : OTerm alpha),
  let source := OriginalUniverseDecoder.source H G M W
  let leaf := OriginalHereditaryLambdaGlobal.closedLeaf endpoint window
    (OriginalTransparentDirectBottom.refined source oldStep)
  Nonempty (Derivation body Delta
    ((graph2 source InternalOriginalStepGuard.one s parameter ⊓
      (graph1 InternalUnpair.left typ s ⊓ graph1 BottomRepresentative.bottomCode t typ)).imp
      (Result leaf s t parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyTargets
