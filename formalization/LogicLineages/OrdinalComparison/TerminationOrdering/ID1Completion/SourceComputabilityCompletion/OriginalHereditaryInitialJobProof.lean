module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialJobTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleInitializationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaStructuralProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialJobProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
theorem actualJob : OriginalHereditaryInitialJobTargets.ActualJob := by
 intro body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job weight B hp hc hr ht hj hs hw hb
 have hi := OriginalInternalJobAdmissibleInitializationProof.initialization body H G M W alpha Delta
   packed parameter typ raw gamma c rawJob typed job hp hc hr ht hj hs
 have ha := andRight (andRight hi)
 have hjob := OriginalHereditaryInternalAgendaBindingProof.jobIntro H M W c B job (numeral 0) typ typed rawJob raw parameter gamma weight
   (andIntro hj (andIntro ht (andIntro hr (andIntro hc (andIntro ha (andIntro hw hb))))))
 exact andIntro (andLeft hi) hjob

theorem actualAgenda : OriginalHereditaryInitialJobTargets.ActualAgenda := by
 intro body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job weight B visit work hp hc hr ht hj hs hw hb hv hwork
 have hi := actualJob body H G M W alpha Delta packed parameter typ raw gamma c rawJob typed job weight B hp hc hr ht hj hs hw hb
 exact OriginalHereditaryInternalAgendaStructuralProof.initial body alpha Delta H M W c B job visit work (andRight hi) hv hwork
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialJobProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInitialJobProof
