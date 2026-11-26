import LogicLineages.PersistentMarking.NumberedWindowSimulationRealizationProof
import LogicLineages.PersistentMarking.NumberedWindowOrdinaryQuoteProof
import LogicLineages.PersistentMarking.NumberedWindowTraceTypingProof

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationQuoteSupport
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowTupleTargets
open NumberedWindowOrdinaryTranslation NumberedWindowPreservationTargets
open NumberedWindowSimulationJobs
open NumberedWindowSimulationRealizationProof

theorem quoteCons {q qs Q Qs} (h : tr q = some Q) (hs : trArgs qs = some Qs) :
    trArgs (.cons q qs) = some (.cons Q Qs) := by
  simp [trArgs,h,hs]

def align {S K C τ q Q T} (h : tr q = some T) (p : TypedTrace S K C τ Q T) :
    TypedTrace S K C q.type Q T := by
  have hR := ((NumberedWindowOrdinaryQuoteProof.term q T h).2 0).1
  rw [realizesAtType hR (NumberedWindowTraceTypingProof.termEnd p)]
  exact p

end LogicLineages.PersistentMarking.NumberedWindowSimulationQuoteSupport
