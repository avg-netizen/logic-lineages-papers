module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowPreservationGuardProof
public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowBindingBaseProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowPreservationBoundProof
open NumberedWindowSyntax NumberedWindowDomain
open NumberedWindowBindingBaseProof

mutual
private theorem shiftAdd (q : NTerm) (a b cutoff : Nat) :
    shift a cutoff (shift b cutoff q) = shift (b+a) cutoff q := by
  cases q with
  | free σ x => rfl
  | bound σ i =>
    by_cases hi : i < cutoff
    · simp only [shift,hi,if_true]
    · have hj : ¬ i+b < cutoff := by omega
      simp only [shift,hi,hj,if_false,Nat.add_assoc]
  | lam σ q => simp only [shift,shiftAdd q]
  | bottom σ => rfl
  | ordinary f bs => simp only [shift,shiftArgsAdd bs]
  | numbered f τ k bs es => simp only [shift,shiftArgsAdd bs,shiftArgsAdd es]
  | auxApp σ τ q a' => simp only [shift,shiftAdd q,shiftAdd a']
termination_by sizeOf q

private theorem shiftArgsAdd (qs : NArgs) (a b cutoff : Nat) :
    shiftArgs a cutoff (shiftArgs b cutoff qs) = shiftArgs (b+a) cutoff qs := by
  cases qs with
  | nil => rfl
  | cons q qs => simp only [shiftArgs,shiftAdd q,shiftArgsAdd qs]
termination_by sizeOf qs
end

private theorem boundUnderBinder (values : NArgs) (σ : Ty) (i d : Nat) :
    substitute values (d+1) (.bound σ (i+1)) =
      shift 1 0 (substitute values d (.bound σ i)) := by
  by_cases hi : i < d
  · have hj : i+1 < d+1 := by omega
    simp only [substitute,hi,hj,if_true,shift,Nat.not_lt_zero,if_false]
  · have hj : ¬ i+1 < d+1 := by omega
    have he : i+1-(d+1) = i-d := by omega
    cases h : values.get (i-d) with
    | some a =>
      simp only [substitute,hi,hj,if_false,he,h,shiftAdd a]
    | none =>
      have hl := Nat.le_trans (getNoneLength values _ h) (Nat.sub_le i d)
      have hs : i+1-values.length = i-values.length+1 := by omega
      simp only [substitute,hi,hj,if_false,he,h,hs,shift,Nat.not_lt_zero]

private theorem shiftWindow {S K C D τ q} {a d : Nat}
    (h : InWindow S K C τ q) (hc : Spine.ShiftCompatible a d C D) :
    InWindow S K D τ (shift a d q) := by
  obtain ⟨_,hs,hh⟩ := NumberedWindowApplicationShiftProof.shape q a d
  exact ⟨NumberedWindowApplicationShiftProof.typed C D q τ a d h.1 hc,
    fun t ht => h.2.1 t (hs ▸ ht),fun f hf => h.2.2 f (hh ▸ hf)⟩

def Compatible (S : Spine.Signature) (K : List Ty) (values : NArgs) (depth : Nat)
    (C D : Spine.BoundContext) : Prop :=
  ∀ i τ, C i = some τ → τ ∈ K → InWindow S K D τ (substitute values depth (.bound τ i))

theorem push {S K values d C D} (hk : DecisionSourceUniverse.Closed K)
    (h : Compatible S K values d C D) :
    Compatible S K values (d+1) (C.push σ) (D.push σ) := by
  intro i τ hi ht
  cases i with
  | zero =>
    have e : σ = τ := Option.some.inj hi
    subst τ
    have hz : 0 < d+1 := by omega
    simp only [substitute,hz,if_true]
    exact ⟨.bound rfl,hk _ ht,fun _ hp => False.elim (List.not_mem_nil hp)⟩
  | succ i =>
    rw [boundUnderBinder]
    exact shiftWindow (h i τ hi ht) (SpineShiftProof.compatibleOne D σ)

theorem one {S K C σ a} (hk : DecisionSourceUniverse.Closed K)
    (h : InWindow S K C σ a) : Compatible S K (.cons a .nil) 0 (C.push σ) C := by
  intro i τ hi ht
  cases i with
  | zero =>
    have e : σ = τ := Option.some.inj hi
    subst τ
    rw [substituteBoundZero]
    exact h
  | succ i =>
    have he : substitute (.cons a .nil) 0 (.bound τ (i+1)) = .bound τ i := by
      simp only [substitute,Nat.not_lt_zero,if_false,Nat.sub_zero,NArgs.get,NArgs.length,
        Nat.add_zero,Nat.add_sub_cancel]
    rw [he]
    exact ⟨.bound hi,hk _ ht,fun _ hp => False.elim (List.not_mem_nil hp)⟩

end LogicLineages.PersistentMarking.NumberedWindowPreservationBoundProof
