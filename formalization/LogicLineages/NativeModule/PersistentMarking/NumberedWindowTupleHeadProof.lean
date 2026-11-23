module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowTupleBridgeProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowTupleHeadProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowTupleTargets
open NumberedWindowApplicationTargets NumberedWindowApplicationPathProof NumberedWindowTupleBridgeProof
open NumberedWindowRealizationShapeProof

theorem ordinary {S : Signature} {K : List Ty} {C : BoundContext} {f : Head}
    {n B : Nat} {τ : Ty} {ds : List Ty} {bs args : Spine.Args} {Bs As : NArgs}
    (hk : DecisionSourceUniverse.Closed K) (hTy : f.result = ArrowPrefix ds τ)
    (hW : InWindow S K C f.result (.ordinary f Bs)) (hAW : ArgsWindow S K C ds As)
    (hBs : RealizesArgs B bs Bs) (hArgs : RealizesArgs B args As) (hn : n ≤ B) :
    Conclusion S K C n τ (.ordinary f Bs) As (.marked f τ bs args) := by
  let M := NTerm.numbered f f.result (n+ds.length) Bs .nil
  have hM : InWindow S K C f.result M := markWindow hW (n+ds.length)
  have hMark : WindowPath S K C f.result (.ordinary f Bs) M :=
    single ⟨.mark,hW,hM⟩
  obtain ⟨start,hStart,hPath⟩ := NumberedWindowApplicationChecks.exact_WholeNumberedAppend S K C ds τ f n Bs .nil As hk
    (by simpa only [← hTy] using hM) hAW
  have hLater : Conclusion S K C n τ M As (.marked f τ bs args) :=
    ⟨start,_,by simpa only [← hTy] using hStart,hPath,
      .marked (Nat.le_refl n) (weakensArgs hn hBs) (weakensArgs hn hArgs)⟩
  exact functionPrefix hk hAW (by rw [← hTy]; exact hMark) hLater

theorem marked {S : Signature} {K : List Ty} {C : BoundContext} {f : Head}
    {n B k : Nat} {σ τ : Ty} {ds : List Ty} {bs es args : Spine.Args} {Bs Es As : NArgs}
    (hk : DecisionSourceUniverse.Closed K) (hTy : σ = ArrowPrefix ds τ)
    (hW : InWindow S K C σ (.numbered f σ k Bs Es)) (hAW : ArgsWindow S K C ds As)
    (hBs : RealizesArgs B bs Bs) (hEs : RealizesArgs B es Es) (hArgs : RealizesArgs B args As)
    (hn : n ≤ B) (hBudget : n+ds.length ≤ k) :
    Conclusion S K C n τ (.numbered f σ k Bs Es) As (.marked f τ bs (es.append args)) := by
  let j := k-ds.length
  have hj : j+ds.length = k := by dsimp [j]; omega
  have hjn : n ≤ j := by dsimp [j]; omega
  obtain ⟨start,hStart,hPath⟩ := NumberedWindowApplicationChecks.exact_WholeNumberedAppend S K C ds τ f j Bs Es As hk
    (by simpa only [← hTy,hj] using hW) hAW
  exact ⟨start,_,by simpa only [← hTy,hj] using hStart,hPath,
    .marked hjn (weakensArgs hn hBs) (appendRealizes _ _ _ _ (weakensArgs hn hEs) (weakensArgs hn hArgs))⟩

end LogicLineages.PersistentMarking.NumberedWindowTupleHeadProof
