module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftOwnProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparseRawTick (chosenTick)
open NumberedWindowInternalSparseRawTickTargets (stateTerm)
open NumberedWindowInternalSparseRawRun (iterateState ownRun)
open NumberedWindowInternalSparseRawRunLiftTargets
open NumberedWindowInternalSparseRawRunShiftProof (shiftLate shiftEarly)
open NumberedWindowInternalSparseRawRunLiftProof (terminalLater runLift)
open NumberedWindowInternalSparseRawRunLiftOwnProof (witnessStrict liftedOwnRun)

theorem exact_OpenRawFirstTickShift : ExactOpenRawFirstTickShift := by
  intro body p other α start next fuel out
  let tick := programGraph (chosenTick p other) next ![start]
  let late := programGraph (iterateState p other) out ![suc fuel,start]
  let early := programGraph (iterateState p other) out ![fuel,next]
  obtain ⟨toEarly⟩ := shiftEarly (body := body) (Γ := [late,tick]) p other start next fuel out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨toLate⟩ := shiftLate (body := body) (Γ := [early,tick]) p other start next fuel out
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction toEarly) (Derivation.implicationIntroduction toLate))⟩

theorem exact_OpenRawTerminalExtraFuel : ExactOpenRawTerminalExtraFuel := by
  intro body p other α flag start fuel more
  let order := ltF fuel more
  let run := programGraph (iterateState p other) (stateTerm flag z) ![fuel,start]
  obtain ⟨d⟩ := terminalLater (body := body) (Γ := [run,order]) p other flag start fuel more
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction d)⟩

theorem exact_OpenRawRunLift : ExactOpenRawRunLift := by
  intro body p other α flag start next fuel more
  let tick := programGraph (chosenTick p other) next ![start]
  let order := ltF fuel more
  let run := programGraph (iterateState p other) (stateTerm flag z) ![fuel,next]
  obtain ⟨d⟩ := runLift (body := body) (Γ := [run,order,tick]) p other flag start next fuel more
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
    ⟨Derivation.hypothesis (List.mem_cons_of_mem _ List.mem_cons_self)⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction (Derivation.implicationIntroduction
    (Derivation.implicationIntroduction d))⟩

theorem exact_OpenFunctionWitnessStrict : ExactOpenFunctionWitnessStrict := by
  intro body α child
  exact witnessStrict (body := body) (Γ := []) child

theorem exact_OpenLiftedOwnRun : ExactOpenLiftedOwnRun := by
  intro body p other α dom cod arg source child dest k
  let run := programGraph (ownRun p other) (suc k) ![source,child,dest]
  obtain ⟨d⟩ := liftedOwnRun (body := body) (Γ := [run]) p other dom cod arg source child dest k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction d⟩

#print axioms exact_OpenRawFirstTickShift
#print axioms exact_OpenRawTerminalExtraFuel
#print axioms exact_OpenRawRunLift
#print axioms exact_OpenFunctionWitnessStrict
#print axioms exact_OpenLiftedOwnRun
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawRunLiftChecks
