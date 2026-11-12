module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomDichotomyDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDichotomyTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors UniformCertificateCompletion
open OriginalTransparentDirectBottomDichotomy
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual selected final checker admits equality or its own exact original
root certificate when the target is literally the same-type bottom. The source
is the original concrete decoder captured before both leaf preparations. No
application-to-bottom identification, erasure transformation, or canonical
ancestor-collapse assertion is included. -/
def ActualOriginalDirectBottomGlobalDichotomy : Prop :=
  ∀ (p : GlobalSourcePackage.Inputs) (H G : Program 1) (W : Program 2) (P : Program 3)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (s t parameter typ : OTerm alpha),
  let source := OriginalTransparentDirectBottomGlobal.source p H G W
  let leaf := (OriginalTransparentDirectBottomGlobal.finalInputs p H G W P).oldStep
  Nonempty (Derivation body Delta
    ((graph2 source InternalOriginalStepGuard.one s parameter ⊓
      (graph1 InternalUnpair.left typ s ⊓ graph1 BottomRepresentative.bottomCode t typ)).imp
      (Result leaf s t parameter)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomGlobalDichotomyTargets
