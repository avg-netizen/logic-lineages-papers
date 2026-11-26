module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All original Code values and contexts, arbitrary annotations and window. -/
def NativeCalibration : Prop := ∀ (n role typ c : Nat)
 (s : OriginalHereditaryWorkBound.State (Fin n)),
 evaluate OriginalHereditaryFuelProgram.fuel (List.Vector.ofFn ![
 OriginalHereditaryAnnotatedExpansion.jobNumber role typ (OriginalHereditaryExpansion.jobNumber c s)]) =
 2 * OriginalHereditaryWorkBound.budget (OriginalHereditaryWorkBound.weight s + 2)
 (OriginalHereditaryWorkBound.weight s)
def RuntimeCalibration : Prop := ∀ (n c : Nat) (a : OriginalHereditaryAgendaDefinitions.Job n),
 evaluate OriginalHereditaryFuelProgram.fuel (List.Vector.ofFn ![OriginalHereditaryRuntimeWork.jobNumber c a]) =
 OriginalHereditaryRuntimeIterationDefinitions.fuel a
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryFuelProgramTargets
