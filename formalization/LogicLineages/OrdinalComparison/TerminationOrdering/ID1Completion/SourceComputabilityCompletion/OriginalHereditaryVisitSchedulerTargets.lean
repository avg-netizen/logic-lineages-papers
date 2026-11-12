module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryVisitScheduler OriginalHereditaryExpansion
open NumberedMultisetNumeric
/-- The existing list mapper adds visit tags without reordering or deduplication. -/
def TagCalibration : Prop := ∀ jobs : List Nat,
  evaluate tagVisits (List.Vector.ofFn ![numbersNumber jobs]) = numbersNumber (jobs.map visitNumber)
/-- Arbitrary old agenda/results; original c is present unchanged in every job
and return frame. This is exactly ONE visit macrostep, not total evaluation. -/
def VisitSimulation : Prop := ∀ (n c : Nat) (s : OriginalHereditaryWorkBound.State (Fin n))
    (agenda results : List Nat),
  evaluate step (List.Vector.ofFn ![stateNumber (visitNumber (jobNumber c s) :: agenda) results]) =
    stateNumber (((OriginalHereditaryWorkBound.successors s).map
      (fun t => visitNumber (jobNumber c t))) ++
      returnNumber (jobNumber c s) (OriginalHereditaryWorkBound.children s.context s.code).length
        s.context.length :: agenda) results
/-- Malformed/unsupported nonzero frame tags and empty agendas are unchanged. -/
def UnsupportedIdentity : Prop :=
  (∀ results : Nat, evaluate step (List.Vector.ofFn ![Nat.pair 0 results]) = Nat.pair 0 results) ∧
  (∀ frame rest results : Nat, (Nat.unpair frame).1 ≠ 0 →
    evaluate step (List.Vector.ofFn ![Nat.pair (1 + Nat.pair frame rest) results]) =
      Nat.pair (1 + Nat.pair frame rest) results)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryVisitSchedulerTargets
