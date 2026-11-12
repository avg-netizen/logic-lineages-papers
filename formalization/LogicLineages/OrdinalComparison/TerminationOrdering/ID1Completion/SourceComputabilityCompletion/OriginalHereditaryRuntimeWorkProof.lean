module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkVisitProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkReturnProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryRuntimeWork OriginalHereditaryAgendaDefinitions
open NumberedMultisetNumeric

theorem stepWork : OriginalHereditaryRuntimeWorkTargets.StepWork := by
  intro R n arity c before after result ht hs
  cases hs with
  | visit a suffix => exact OriginalHereditaryRuntimeWorkVisitProof.visitWork R c a suffix result
  | returning a suffix =>
    have ha : OriginalHereditaryTypedJobDefinitions.Typed arity a :=
      ht (.returning a) List.mem_cons_self
    unfold agendaNumber
    rw [List.map_cons,frameNumber,numbersNumber]
    exact OriginalHereditaryRuntimeWorkReturnProof.returnWork R arity c a ha _ result

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryRuntimeWorkProof
