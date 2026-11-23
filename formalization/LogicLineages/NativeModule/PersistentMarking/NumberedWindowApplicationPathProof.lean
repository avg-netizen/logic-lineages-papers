module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowApplicationDomainProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowApplicationPathProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowApplicationTargets
open NumberedWindowApplicationDomainProof

theorem endpoints {S : Signature} {K : List Ty} {C : BoundContext} {τ : Ty} {Q R : NTerm}
    (h : WindowPath S K C τ Q R) : InWindow S K C τ Q ∧ InWindow S K C τ R := by
  induction h with
  | refl h => exact ⟨h,h⟩
  | next hs _ ih => exact ⟨hs.2.1,ih.2⟩

theorem trans {S : Signature} {K : List Ty} {C : BoundContext} {τ : Ty} {Q R T : NTerm}
    (hQR : WindowPath S K C τ Q R) (hRT : WindowPath S K C τ R T) :
    WindowPath S K C τ Q T := by
  induction hQR with
  | refl _ => exact hRT
  | next e _ ih => exact .next e (ih hRT)

theorem single {S : Signature} {K : List Ty} {C : BoundContext} {τ : Ty} {Q R : NTerm}
    (h : WindowStep S K C τ Q R) : WindowPath S K C τ Q R :=
  .next h (.refl h.2.2)

theorem applicationsWindow : ApplicationsInWindow := by
  intro S K C ds τ Q As hk hQ hAs
  induction hAs generalizing Q with
  | nil => exact ⟨_,rfl,hQ⟩
  | cons hA _ ih =>
    obtain ⟨start,hcall,hw⟩ := ih _ (app S K C _ _ _ _ hk hQ hA)
    exact ⟨start,(appEq hQ.1 hA.1 _).trans hcall,hw⟩

theorem liftOne : LiftAuxFunction := by
  intro S K C σ τ Q R A hk hPath hA
  induction hPath with
  | refl hQ => exact .refl (app S K C σ τ _ A hk hQ hA)
  | next step _ ih =>
    exact .next ⟨RawStep.auxFunction step.1,app S K C σ τ _ A hk step.2.1 hA,
      app S K C σ τ _ A hk step.2.2 hA⟩ ih

theorem lift : LiftApplications := by
  intro S K C ds τ Q R As hk hPath hAs
  induction hAs generalizing Q R with
  | nil => exact ⟨_,_,rfl,rfl,hPath⟩
  | cons hA _ ih =>
    have hends := endpoints hPath
    obtain ⟨start,out,hs,ht,h⟩ := ih _ _ (liftOne S K C _ _ _ _ _ hk hPath hA)
    exact ⟨start,out,(appEq hends.1.1 hA.1 _).trans hs,(appEq hends.2.1 hA.1 _).trans ht,h⟩

end LogicLineages.PersistentMarking.NumberedWindowApplicationPathProof
