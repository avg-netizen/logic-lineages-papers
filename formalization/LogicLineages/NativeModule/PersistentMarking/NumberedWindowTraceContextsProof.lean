module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTraceBudgetTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowTraceContextsProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowPreservationTargets NumberedWindowClosing
open NumberedWindowTraceAlgebra NumberedWindowTraceBudgetTargets

theorem lambda : LiftTypedLambda := by
  intro S K C σ τ q r tr
  induction tr with
  | done ht => exact ⟨.done (.lam ht),rfl,rfl⟩
  | raw hq hr hs rest ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.raw (.lam hq) (.lam hr) (.lam hs) out,
      by simp only [vertices,List.map_cons,hv],by simp only [rawLength,hl]⟩
  | equiv he _ ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.equiv (.lam he) out,by simp only [vertices,List.map_cons,hv],hl⟩

theorem auxiliaryFn : LiftTypedAuxFunction := by
  intro S K C σ τ a q r ha tr
  induction tr with
  | done ht => exact ⟨.done (.auxApp ht ha),rfl,rfl⟩
  | raw hq hr hs rest ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.raw (.auxApp hq ha) (.auxApp hr ha) (.auxFunction hs) out,
      by simp only [vertices,List.map_cons,hv],by simp only [rawLength,hl]⟩
  | equiv he _ ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.equiv (.appFunction he ha) out,by simp only [vertices,List.map_cons,hv],hl⟩

theorem fromWindowPath : WindowPathAsRawTrace := by
  intro S K C τ q r path
  induction path with
  | refl h => exact ⟨.done h.1,True.intro⟩
  | next h _ ih =>
    obtain ⟨out,hr⟩ := ih
    exact ⟨.raw h.2.1.1 h.2.2.1 h.1 out,hr⟩

theorem ordinaryBase : LiftTypedOrdinaryBase := by
  intro S K C f bs cs tr
  induction tr with
  | done ht => exact ⟨.done (.ordinary ht),rfl,rfl⟩
  | raw hq hr hs rest ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.raw (.ordinary hq) (.ordinary hr) (.ordinaryBase hs) out,
      by simp only [vertices,argsVertices,List.map_cons,hv],by simp only [rawLength,argsRawLength,hl]⟩
  | equiv he _ ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.equiv (.ordinaryArguments he) out,
      by simp only [vertices,argsVertices,List.map_cons,hv],hl⟩

end LogicLineages.PersistentMarking.NumberedWindowTraceContextsProof
