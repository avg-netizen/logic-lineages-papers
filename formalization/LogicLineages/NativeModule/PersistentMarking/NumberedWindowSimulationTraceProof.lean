module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowSimulationJobs
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceJoinProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationChecks

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowSimulationTraceProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowClosing
open NumberedWindowPreservationTargets NumberedWindowSimulationData
open NumberedWindowPositiveSimulationTargets NumberedWindowSimulationJobs
open NumberedWindowOrdinaryTranslation

theorem admittedStart {S K C τ Q T} (path : TypedTrace S K C τ Q T)
    (h : AdmittedTrace path) : InWindow S K C τ Q := by
  cases path <;> exact h _ List.mem_cons_self

theorem admittedEnd {S K C τ Q T} (path : TypedTrace S K C τ Q T)
    (h : AdmittedTrace path) : InWindow S K C τ T := by
  induction path with
  | done ht => exact h _ List.mem_cons_self
  | raw _ _ _ _ ih => exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))
  | equiv _ _ ih => exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem weakOfTrace {S K τ Q T t}
    (hk : DecisionSourceUniverse.Closed K) (hQ : InWindow S K E τ Q)
    (ht : tr t = some T) (path : TypedTrace S K E τ Q T) : WeakResult S K τ Q t :=
  ⟨T,ht,path,NumberedWindowPreservationChecks.exact_AllTypedTraceIntermediates S K E τ Q T hk hQ path⟩

theorem prepend {S K τ Q R t} (hQ : InWindow S K E τ Q)
    (hR : InWindow S K E τ R) (hs : RawStep S K Q R)
    (h : WeakResult S K τ R t) : WeakResult S K τ Q t := by
  obtain ⟨T,ht,path,hw⟩ := h
  refine ⟨T,ht,.raw hQ.1 hR.1 hs path,?_⟩
  intro p hp
  simp only [vertices,List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hQ
  · exact hw p hp

theorem prependFromContinuation {S K τ Q R t} (hQ : InWindow S K E τ Q)
    (hs : RawStep S K Q R) (h : WeakResult S K τ R t) : WeakResult S K τ Q t := by
  obtain ⟨T,ht,path,hw⟩ := h
  exact prepend hQ (admittedStart path hw) hs ⟨T,ht,path,hw⟩

theorem prependTyped {S K τ Q R t} (hk : DecisionSourceUniverse.Closed K)
    (hQ : InWindow S K E τ Q) (prefixPath : TypedTrace S K E τ Q R)
    (h : WeakResult S K τ R t) : WeakResult S K τ Q t := by
  obtain ⟨T,ht,path,_⟩ := h
  obtain ⟨whole,_,_⟩ := NumberedWindowTraceJoinProof.termJoin S K E τ Q R T prefixPath path
  exact weakOfTrace hk hQ ht whole

theorem strictly {S K τ Q t} (h : PreparedStrict S K τ Q t) : StrictResult S K τ Q t := by
  obtain ⟨R,_hd,hs,hQ,hR,T,ht,path,hw⟩ := h
  refine ⟨T,ht,.raw hQ.1 hR.1 hs path,?_,Nat.zero_lt_succ _⟩
  intro p hp
  simp only [vertices,List.mem_cons] at hp
  rcases hp with rfl | hp
  · exact hQ
  · exact hw p hp

end LogicLineages.PersistentMarking.NumberedWindowSimulationTraceProof
