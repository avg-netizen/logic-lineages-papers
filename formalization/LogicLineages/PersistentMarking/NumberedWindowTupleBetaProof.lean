import LogicLineages.PersistentMarking.NumberedWindowTupleBridgeProof

namespace LogicLineages.PersistentMarking.NumberedWindowTupleBetaProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules
open NumberedWindowApplicationTargets NumberedWindowTupleBridgeProof
open NumberedWindowApplicationPathProof NumberedWindowApplicationDomainProof

theorem prependBeta {S : Signature} {K : List Ty} {C : BoundContext}
    {n : Nat} {σ β τ : Ty} {ds : List Ty} {Body A : NTerm} {Vs Tail : NArgs} {r : Expr}
    (hk : DecisionSourceUniverse.Closed K) (hTy : β = ArrowPrefix ds τ)
    (hLam : InWindow S K C (.arrow σ β)
      (.lam σ (NumberedWindowSyntax.substitute Vs 1 Body)))
    (hA : InWindow S K C σ A)
    (hBody : InWindow S K C β (NumberedWindowSyntax.substitute (.cons A Vs) 0 Body))
    (hTail : ArgsWindow S K C ds Tail)
    (restProof : Conclusion S K C n τ (NumberedWindowSyntax.substitute (.cons A Vs) 0 Body) Tail r) :
    Conclusion S K C n τ (.lam σ (NumberedWindowSyntax.substitute Vs 1 Body)) (.cons A Tail) r := by
  have hRaw : RawStep S K (.auxApp σ β (.lam σ (NumberedWindowSyntax.substitute Vs 1 Body)) A)
      (NumberedWindowSyntax.substitute (.cons A Vs) 0 Body) := by
    rw [← NumberedWindowBindingChecks.exact_SinglePushBlock A Vs 0 Body]
    exact .beta
  have hBeta : WindowPath S K C β
      (.auxApp σ β (.lam σ (NumberedWindowSyntax.substitute Vs 1 Body)) A)
      (NumberedWindowSyntax.substitute (.cons A Vs) 0 Body) :=
    single ⟨hRaw,app S K C σ β _ A hk hLam hA,hBody⟩
  obtain ⟨start,out,hs,hp,hr⟩ := functionPrefix hk hTail (by rw [← hTy]; exact hBeta) restProof
  exact ⟨start,out,(appEq hLam.1 hA.1 Tail).trans hs,hp,hr⟩

end LogicLineages.PersistentMarking.NumberedWindowTupleBetaProof
