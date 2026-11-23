module

public import LogicLineages.NativeModule.PersistentMarking.ObservationLambdaTargets
public import LogicLineages.NativeModule.PersistentMarking.InsertionProof

@[expose] public section

namespace LogicLineages.PersistentMarking.ObservationOpeningProof
open Spine NameBridge DecisionInventory DecisionPorts DecisionObservations ObservationLambda

theorem boundCoherence (vs : Args) (σ : Ty) (x d : Nat) (τ : Ty) (i : Nat) (hv : FreeValues vs) :
    substitute (.cons (.free σ x) .nil) d (substitute vs (d+1) (.bound τ i)) =
    substitute (.cons (.free σ x) vs) d (.bound τ i) := by
  by_cases hi : i < d
  · have hi' : i < d+1 := by omega
    simp [substitute,hi,hi']
  · by_cases he : i = d
    · subst i; simp [substitute,Args.get,shift]
    · have hgt : ¬i < d+1 := by omega
      have hn : i-d = (i-(d+1))+1 := by omega
      cases hl : vs.get (i-(d+1)) with
      | some v =>
        obtain ⟨υ,y,rfl⟩ := hv _ v hl
        simp [substitute,hi,hgt,hn,Args.get,hl,shift]
      | none =>
        have hlen := InsertionProof.getNoneLength vs (i-(d+1)) hl
        have hj : ¬i-vs.length < d := by omega
        have hh : i-vs.length-1 = i-(1+vs.length) := by omega
        cases hk : i-vs.length-d with
        | zero => omega
        | succ k => simp only [substitute,if_neg hi,if_neg hgt,hn,Args.get,hl,if_neg hj,hk,Args.length,hh]
mutual
 theorem coherence (vs : Args) (σ : Ty) (x d : Nat) (q : Expr) (hv : FreeValues vs) :
    substitute (.cons (.free σ x) .nil) d (substitute vs (d+1) q) =
    substitute (.cons (.free σ x) vs) d q := by
  cases q with
  | free τ y => rfl
  | bound τ i => exact boundCoherence vs σ x d τ i hv
  | lam τ q => simp only [substitute,coherence vs σ x (d+1) q hv]
  | head f bs => simp only [substitute,coherenceArgs vs σ x d bs hv]
  | marked f τ bs es => simp only [substitute,coherenceArgs vs σ x d bs hv,coherenceArgs vs σ x d es hv]
 termination_by sizeOf q
 theorem coherenceArgs (vs : Args) (σ : Ty) (x d : Nat) (qs : Args) (hv : FreeValues vs) :
    substituteArgs (.cons (.free σ x) .nil) d (substituteArgs vs (d+1) qs) =
    substituteArgs (.cons (.free σ x) vs) d qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [substituteArgs,coherence vs σ x d q hv,coherenceArgs vs σ x d qs hv]
 termination_by sizeOf qs
end

theorem reflection (vs : Args) (q : Expr) (σ : Ty) (body : Expr) (hv : FreeValues vs)
    (h : openOccurrence vs q = .lam σ body) :
    ∃ originalBody, q = .lam σ originalBody ∧ body = substitute vs 1 originalBody := by
  cases q with
  | free τ y => cases h
  | bound τ i =>
    cases hl : vs.get i with
    | none => simp [openOccurrence,substitute,hl] at h
    | some v =>
      obtain ⟨υ,y,rfl⟩ := hv i v hl
      simp [openOccurrence,substitute,hl,shift] at h
  | lam τ q =>
    simp only [openOccurrence,substitute,Expr.lam.injEq] at h
    obtain ⟨rfl,hb⟩ := h
    exact ⟨q,rfl,hb.symm⟩
  | head f bs => cases h
  | marked f τ bs es => cases h
end LogicLineages.PersistentMarking.ObservationOpeningProof
