module

public import LogicLineages.NativeModule.PersistentMarking.RefinementFreeBlockProof

@[expose] public section

namespace LogicLineages.PersistentMarking.RefinementFreeCallProof
open Spine NameBridge

theorem success (q : Expr) (args vs ws : Args) (r : Expr) (h : applyAux q args vs = some r) :
    ∃ r', applyAux q args ws = some r' := by
  cases args with
  | nil => exact ⟨substitute ws 0 q,by simp only [applyAux]⟩
  | cons a rest =>
    cases q with
    | free σ x => simp [applyAux] at h
    | bound σ i => simp [applyAux] at h
    | lam σ q =>
      by_cases ht : a.type=σ
      · simp only [applyAux,ht,if_true] at h ⊢
        exact success q rest (.cons a vs) (.cons a ws) r h
      · simp [applyAux,ht] at h
    | head f base =>
      cases hc : consumeTypes f.result (.cons a rest) with
      | none => simp [applyAux,hc] at h
      | some τ => exact ⟨.marked f τ (substituteArgs ws 0 base) (.cons a rest),by simp [applyAux,hc]⟩
    | marked f σ base extras =>
      cases hc : consumeTypes σ (.cons a rest) with
      | none => simp [applyAux,hc] at h
      | some τ => exact ⟨.marked f τ (substituteArgs ws 0 base) ((substituteArgs ws 0 extras).append (.cons a rest)),by simp [applyAux,hc]⟩
termination_by sizeOf args

theorem aux (σ : Ty) (x : Nat) (q : Expr) (args vs : Args) :
    applyAux (substitute (.cons (.free σ x) .nil) vs.length q) args vs =
      applyAux q args (vs.append (.cons (.free σ x) .nil)) := by
  cases args with
  | nil =>
    simpa only [applyAux,Nat.zero_add] using congrArg some (RefinementFreeBlockProof.block vs 0 σ x q)
  | cons a rest =>
    cases q with
    | free τ y => simp only [substitute,applyAux]
    | bound τ i =>
      by_cases hi : i < vs.length
      · simp [substitute,hi,applyAux]
      · cases hn : i-vs.length with
        | zero => simp [substitute,hi,hn,Args.get,shift,applyAux]
        | succ n => simp [substitute,hi,hn,Args.get,applyAux]
    | lam τ q =>
      by_cases ht : a.type=τ
      · have hd : vs.length+1 = (Args.cons a vs).length := by simp [Args.length,Nat.add_comm]
        simp only [substitute,applyAux,ht,if_true,hd]
        exact aux σ x q rest (.cons a vs)
      · simp [substitute,applyAux,ht]
    | head f base =>
      simp only [substitute,applyAux]
      have hb := RefinementFreeBlockProof.blockArgs vs 0 σ x base
      simp only [Nat.zero_add] at hb
      rw [hb]
    | marked f τ base extras =>
      simp only [substitute,applyAux]
      have hb := RefinementFreeBlockProof.blockArgs vs 0 σ x base
      have he := RefinementFreeBlockProof.blockArgs vs 0 σ x extras
      simp only [Nat.zero_add] at hb he
      rw [hb,he]
termination_by sizeOf args

theorem call (σ : Ty) (x : Nat) (q : Expr) (args : Args) :
    apply (.lam σ q) (.cons (.free σ x) args) = apply (openBody σ x q) args := by
  cases args with
  | nil => simp [apply,applyAux,Expr.type,openBody]
  | cons a rest =>
    simpa only [apply,applyAux,Expr.type,ite_true,openBody,Args.length,Args.append] using
      (aux σ x q (.cons a rest) .nil).symm

theorem accumulatorSuccess : RefinementFullCallTargets.AccumulatorSuccess := success
theorem freeOpeningAux : RefinementFullCallTargets.FreeOpeningAux := aux
theorem freeOpeningCall : RefinementFullCallTargets.FreeOpeningCall := call
end LogicLineages.PersistentMarking.RefinementFreeCallProof
