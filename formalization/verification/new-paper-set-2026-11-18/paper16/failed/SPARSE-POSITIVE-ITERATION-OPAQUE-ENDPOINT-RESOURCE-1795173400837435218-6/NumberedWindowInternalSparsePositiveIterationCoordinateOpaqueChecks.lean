module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueTransportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open NumberedWindowInternalSparsePositiveFold (iterateStep)
open NumberedWindowInternalSparsePositiveFoldTargets (stepGraph)
open NumberedWindowInternalSparsePositiveIterationTargets
open NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueTransportProof (moveUnused)

attribute [local irreducible] programGraph iterateStep

theorem exact_OpenStepCoordinates : OpenStepCoordinates := by
  intro body raw least α out prior c ty k start cert k' start' cert'
  let a := stepGraph raw least out k prior c ty start cert
  let b := stepGraph raw least out k' prior c ty start' cert'
  have ha : Derivation body [a] a := Derivation.hypothesis List.mem_cons_self
  have hb : Derivation body [b] b := Derivation.hypothesis List.mem_cons_self
  obtain ⟨forward⟩ := moveUnused raw least out prior c ty k start cert k' start' cert' ⟨ha⟩
  obtain ⟨backward⟩ := moveUnused raw least out prior c ty k' start' cert' k start cert ⟨hb⟩
  exact ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction forward)
    (Derivation.implicationIntroduction backward)⟩

#print axioms exact_OpenStepCoordinates
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveIterationCoordinateOpaqueChecks
