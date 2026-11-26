import LogicLineages.PersistentMarking.NumberedWindowTraceBudgetTargets

namespace LogicLineages.PersistentMarking.NumberedWindowTraceJoinProof
open NumberedWindowPreservationTargets NumberedWindowClosing
open NumberedWindowTraceAlgebra NumberedWindowTraceBudgetTargets

theorem termVertices : LiteralTermVertices := by
  intro S K C τ q r t
  induction t with
  | done ht => rfl
  | raw _ _ _ _ ih => simp only [vertices,termSources,List.cons_append,ih]
  | equiv _ _ ih => simp only [vertices,termSources,List.cons_append,ih]

theorem listVertices : LiteralArgsVertices := by
  intro S K C types qs rs t
  induction t with
  | done ht => rfl
  | raw _ _ _ _ ih => simp only [argsVertices,argsSources,List.cons_append,ih]
  | equiv _ _ ih => simp only [argsVertices,argsSources,List.cons_append,ih]

theorem termJoin : JoinTermTraces := by
  intro S K C τ q r t left
  induction left with
  | done ht =>
    intro right
    exact ⟨right,rfl,by simp only [rawLength,Nat.zero_add]⟩
  | raw hq hr hs rest ih =>
    intro right
    obtain ⟨out,hv,hl⟩ := ih right
    refine ⟨.raw hq hr hs out,by simp only [vertices,termSources,List.cons_append,hv],?_⟩
    simp only [rawLength,hl]
    omega
  | equiv he rest ih =>
    intro right
    obtain ⟨out,hv,hl⟩ := ih right
    exact ⟨.equiv he out,by simp only [vertices,termSources,List.cons_append,hv],hl⟩

theorem argsJoin : JoinArgsTraces := by
  intro S K C types qs rs ts left
  induction left with
  | done ht =>
    intro right
    exact ⟨right,rfl,by simp only [argsRawLength,Nat.zero_add]⟩
  | raw hq hr hs rest ih =>
    intro right
    obtain ⟨out,hv,hl⟩ := ih right
    refine ⟨.raw hq hr hs out,by simp only [argsVertices,argsSources,List.cons_append,hv],?_⟩
    simp only [argsRawLength,hl]
    omega
  | equiv he rest ih =>
    intro right
    obtain ⟨out,hv,hl⟩ := ih right
    exact ⟨.equiv he out,by simp only [argsVertices,argsSources,List.cons_append,hv],hl⟩

end LogicLineages.PersistentMarking.NumberedWindowTraceJoinProof
