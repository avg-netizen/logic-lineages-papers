module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingRawProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingPrimaryThinProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingTraceThinProof
open NumberedWindowSyntax NumberedWindowClosing NumberedWindowPreservationTargets

theorem trace {S K n d C D τ q r} (hc : CloseCompatible n d C D)
    (tr : TypedTrace S K C τ q r) :
    ∃ out : TypedTrace S K D τ (closeAt n d q) (closeAt n d r),
      vertices out = (vertices tr).map (closeAt n d) ∧ rawLength out = rawLength tr := by
  induction tr with
  | done ht =>
    exact ⟨.done (NumberedWindowClosingTypedThinCore.term n d C D _ τ ht hc),rfl,rfl⟩
  | raw hq hr hStep t ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.raw (NumberedWindowClosingTypedThinCore.term n d C D _ τ hq hc)
      (NumberedWindowClosingTypedThinCore.term n d C D _ τ hr hc)
      (NumberedWindowClosingRawProof.term n hStep d) out,
      by simp only [vertices,List.map_cons,hv],by simp only [rawLength,hl]⟩
  | equiv hPrim t ih =>
    obtain ⟨out,hv,hl⟩ := ih
    exact ⟨.equiv (NumberedWindowClosingPrimaryThinProof.term n hPrim d D hc) out,
      by simp only [vertices,List.map_cons,hv],hl⟩

end LogicLineages.PersistentMarking.NumberedWindowClosingTraceThinProof
