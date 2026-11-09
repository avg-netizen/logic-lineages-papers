module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.TypedSpineDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeast
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Original Object = pair(original Gamma, original raw packed bottom).
Inputs are [original type code,arbitrary original Gamma code]. The original
total Object codec needs no successful Gamma decoder premise. -/
def bottomObject : Program 2 :=
  pairOf (.projection 1)
    (.composition BottomRepresentative.bottomCode (fun _ : Fin 1 => .projection 0))

def bottomGraph {α : Type} (out typ gammaCode : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 bottomObject out typ gammaCode

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.ComputabilityLeast
