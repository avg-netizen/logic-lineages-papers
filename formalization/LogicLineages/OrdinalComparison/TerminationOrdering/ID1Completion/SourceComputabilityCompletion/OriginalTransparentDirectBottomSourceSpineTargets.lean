module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Concrete original source acceptance and actual nonbottom discharge the complete spine guard to an actual bottom target. No tag or depth hypothesis. -/
def ActualConcreteSourceBottomSpine : Prop :=
  ∀ (H G : Program 1) (M W : Program 2)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t cert parameter typ : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 (OriginalUniverseDecoder.source H G M W) InternalOriginalStepGuard.one s parameter ⊓
      ((BottomRepresentative.bottomGraph InternalOriginalStepGuard.one s).not ⊓
        graph1 BottomRepresentative.bottomCode t typ)).imp
      (graph4 (PositiveGuard.spineGuard BottomSpineMeasure.measure) InternalOriginalStepGuard.one s t cert parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomSourceSpineTargets
