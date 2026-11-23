module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowReservedMarkShapeProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationRawProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowReservedMarkWindowProof
open NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTraceBudgetTargets

private theorem typed {q r} (h : MarkDecrease q r) :
    ∀ C τ, Typed C q τ → Typed C r τ := by
  induction h with
  | omega =>
    intro C τ ht
    cases ht with
    | ordinary hb => exact .numbered hb .nil
  | finite _ =>
    intro C τ ht
    cases ht with
    | numbered hb he => exact .numbered hb he
  | lam _ ih =>
    intro C τ ht
    cases ht with
    | lam hb => exact .lam (ih _ _ hb)

theorem reserved : OneReservedMarkStep := by
  intro S K C τ n q r Q hk hm hQ hWin
  obtain ⟨R,hd,hs,hR⟩ := NumberedWindowReservedMarkShapeProof.step S K n q r Q hm hQ
  exact ⟨R,hd,hs,NumberedWindowPreservationRawProof.raw hk hWin (typed hd C τ hWin.1) hs,hR⟩

end LogicLineages.PersistentMarking.NumberedWindowReservedMarkWindowProof
