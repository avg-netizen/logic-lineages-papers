import LogicLineages.PersistentMarking.NumberedWindowTraceTypingProof
import LogicLineages.PersistentMarking.NumberedWindowTraceJoinProof

namespace LogicLineages.PersistentMarking.NumberedWindowTraceConsProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowPreservationTargets NumberedWindowClosing
open NumberedWindowTraceAlgebra NumberedWindowTraceBudgetTargets
open NumberedWindowTraceTypingProof

private theorem headTrace {S K C σ q r types qs}
    (tr : TypedTrace S K C σ q r) (hs : BaseTyped C qs types) :
    ∃ out : ArgsTrace S K C (σ::types) (.cons q qs) (.cons r qs),
      argsSources out = (termSources tr).map (fun t => .cons t qs) ∧
      argsRawLength out = rawLength tr := by
  induction tr with
  | done ht => exact ⟨.done (.cons ht hs),rfl,rfl⟩
  | raw hq hr hp rest ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.raw (.cons hq hs) (.cons hr hs) (.first hp) out,
      by simp only [argsSources,termSources,List.map_cons,hv],
      by simp only [rawLength,argsRawLength,hl]⟩
  | equiv he _ ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.equiv (.cons he (orderedRefl S K C qs types hs)) out,
      by simp only [argsSources,termSources,List.map_cons,hv],hl⟩

private theorem tailTrace {S K C σ r types qs rs}
    (tr : ArgsTrace S K C types qs rs) (hr : Typed C r σ) :
    ∃ out : ArgsTrace S K C (σ::types) (.cons r qs) (.cons r rs),
      argsVertices out = (argsVertices tr).map (.cons r) ∧
      argsRawLength out = argsRawLength tr := by
  induction tr with
  | done ht => exact ⟨.done (.cons hr ht),rfl,rfl⟩
  | raw hq hs hp rest ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.raw (.cons hr hq) (.cons hr hs) (.later hp) out,
      by simp only [argsVertices,List.map_cons,hv],by simp only [argsRawLength,hl]⟩
  | equiv he _ ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.equiv (.cons (.refl hr) he) out,
      by simp only [argsVertices,List.map_cons,hv],hl⟩

theorem cons : ConsTypedTrace := by
  intro S K C σ types q r qs rs first tail
  obtain ⟨head,hv,hl⟩ := headTrace first (argsStart tail)
  obtain ⟨rest,ht,hs⟩ := tailTrace tail (termEnd first)
  obtain ⟨out,hw,hk⟩ := NumberedWindowTraceJoinProof.argsJoin S K C (σ::types) _ _ _ head rest
  exact ⟨out,by rw [hw,hv,ht],by rw [hk,hl,hs]⟩

end LogicLineages.PersistentMarking.NumberedWindowTraceConsProof
