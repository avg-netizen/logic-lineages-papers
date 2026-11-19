import LogicLineages.PersistentMarking.NumberedWindowPreservationTargets
import LogicLineages.PersistentMarking.NumberedWindowPreservationRawProof
import LogicLineages.PersistentMarking.NumberedWindowPreservationPrimaryProof

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationChecks
open NumberedWindowDomain NumberedWindowPreservationTargets

theorem exact_RawTypedAdmissibility : RawTypedAdmissibility := by
  intro S K C τ q r hk hq hr hs
  exact NumberedWindowPreservationRawProof.raw hk hq hr hs

theorem exact_PrimaryAdmissibility : PrimaryAdmissibility := by
  intro S K C τ q r hk h
  exact NumberedWindowPreservationPrimaryProof.primary hk h

private theorem all {S K C τ q t} (hk : DecisionSourceUniverse.Closed K)
    (trace : TypedTrace S K C τ q t) :
    InWindow S K C τ q → ∀ r ∈ vertices trace, InWindow S K C τ r := by
  induction trace with
  | done _ =>
    intro h r hr
    simp only [vertices,List.mem_singleton] at hr
    subst r
    exact h
  | raw _ ht hs _ ih =>
    intro h r hr
    simp only [vertices,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h
    · exact ih (NumberedWindowPreservationRawProof.raw hk h ht hs) r hr
  | equiv he _ ih =>
    intro h r hr
    simp only [vertices,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact h
    · exact ih ((NumberedWindowPreservationPrimaryProof.primary hk he).mp h) r hr

theorem exact_AllTypedTraceIntermediates : AllTypedTraceIntermediates := by
  intro S K C τ q t hk h trace
  exact all hk trace h

#print axioms exact_RawTypedAdmissibility
#print axioms exact_PrimaryAdmissibility
#print axioms exact_AllTypedTraceIntermediates

end LogicLineages.PersistentMarking.NumberedWindowPreservationChecks
