module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryAnnotatedVisit OriginalHereditaryVisitScheduler (stateNumber visitNumber returnNumber)
open NumberedMultisetNumeric NumberedLeastCodeRepresentative
def FrameCalibration : Prop := ∀ f : Nat,
  evaluate forgetFrame (List.Vector.ofFn ![f]) = forgetFrameNumber f
def StateCalibration : Prop := ∀ (agenda results : List Nat),
  evaluate forgetState (List.Vector.ofFn ![stateNumber agenda results]) =
    stateNumber (agenda.map forgetFrameNumber) results
/-- Role/type are retained in the parent return frame, while counts and all raw
jobs project to the checked raw visit step. Results are untouched. -/
def VisitSimulation : Prop := ∀ (n c role typ : Nat)
    (s : OriginalHereditaryWorkBound.State (Fin n)) (agenda results : List Nat),
  let j := OriginalHereditaryAnnotatedExpansion.jobNumber role typ (OriginalHereditaryExpansion.jobNumber c s)
  evaluate step (List.Vector.ofFn ![stateNumber (visitNumber j :: agenda) results]) =
    stateNumber ((OriginalHereditaryAnnotatedExpansion.values role typ (codeNumber s.code)
      ((OriginalHereditaryWorkBound.successors s).map (OriginalHereditaryExpansion.jobNumber c))).map visitNumber ++
      returnNumber j (OriginalHereditaryWorkBound.children s.context s.code).length s.context.length :: agenda) results
/-- Exact commuting square of executable one-visit steps. It is NOT return
assembly, total evaluation, source closure, or a primitive operation bound. -/
def ForgettingSimulation : Prop := ∀ (n c role typ : Nat)
    (s : OriginalHereditaryWorkBound.State (Fin n)) (agenda results : List Nat),
  let j := OriginalHereditaryAnnotatedExpansion.jobNumber role typ (OriginalHereditaryExpansion.jobNumber c s)
  evaluate forgetState (List.Vector.ofFn ![evaluate step
    (List.Vector.ofFn ![stateNumber (visitNumber j :: agenda) results])]) =
    evaluate OriginalHereditaryVisitScheduler.step (List.Vector.ofFn ![
      stateNumber (visitNumber (OriginalHereditaryExpansion.jobNumber c s) ::
        agenda.map forgetFrameNumber) results])

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedVisitTargets
