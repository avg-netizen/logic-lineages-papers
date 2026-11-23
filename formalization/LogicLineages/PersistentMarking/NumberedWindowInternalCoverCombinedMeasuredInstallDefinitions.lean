module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedRestrictedMeasuredClassApplicationTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCanonicalAddressTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseApplicationFrontendTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstall
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalCoverRefinedInductionDispatchTargets (Programs)
open NumberedWindowInternalCoverCombinedRestrictedTargets (combinedPrograms)
open NumberedWindowInternalCoverCombinedRestrictedWrapperTargets (thinMatchingWindow)
open NumberedWindowInternalCoverCombinedRestrictedDirectedXTargets (directedX)
open NumberedWindowInternalCoverCombinedRestrictedPairedAuxTargets (thinPairedExchange)
open NumberedWindowInternalMeasuredAuxExchangeTargets (measuredExchange)
open NumberedWindowInternalAuxMeasureMemoTargets (selectedMeasure)
open NumberedWindowInternalSparseCoverGuardedExchangeTargets (guardedExchange)
open NumberedWindowInternalSparseScalarEdge (edge4)
open NumberedWindowInternalSparsePackedLeast (membersAtSeed packedLeastProgram)
open NumberedWindowInternalSparseTypedRaw (typedRaw5)
open NumberedWindowInternalSparseCanonicalAddressTargets (addressScalar)
open NumberedWindowInternalSparseApplicationFrontend (applicationGuard)

/-- Executable components of one combined route. The constructor below fixes
every field; this record adds no mathematical supplier or assumed law. -/
structure Route where
  source : Programs
  window : Program 3
  exchange : Program 2
  edge : Program 4
  members : Program 3
  least : Program 3
  raw : Program 5
  scalar : Program 1
  application : Program 3

/-- Install the measured, paired, cover-guarded exchange in every class
computation and in the actual address/application frontends. The combined
syntax, shared measure, cover, and original window remain the same. -/
def install (s : Settings) (V TV M M0 : Program 1) (B : Program 2)
    (T : Program 1) (base : Program 2) (cv tv : Program 1)
    (root other : Program 3) : Route :=
  let P := combinedPrograms s V TV M M0 B T
  let W := thinMatchingWindow P.cover s P.W P.V
  let X := guardedExchange P.cover s
    (thinPairedExchange (measuredExchange (selectedMeasure P.R) (directedX base P.V)))
  let L := packedLeastProgram P.cover X W s
  let I := addressScalar cv tv W L
  { source := P
    window := W
    exchange := X
    edge := edge4 X W
    members := membersAtSeed P.cover X W s
    least := L
    raw := typedRaw5 root other W P.V
    scalar := I
    application := applicationGuard I L }

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverCombinedMeasuredInstall
