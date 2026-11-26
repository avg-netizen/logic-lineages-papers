module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowClosingOperationsProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowClosingShiftProof
open NumberedWindowSyntax NumberedWindowClosing
open NameBridge (Name)

mutual
theorem term (n : Name) (d amount cutoff : Nat) (h : cutoff ≤ d) (q : NTerm) :
    closeAt n (d+amount) (shift amount cutoff q) = shift amount cutoff (closeAt n d q) := by
  cases q with
  | free σ x =>
    have hlt := Nat.not_lt.mpr h
    by_cases he : (σ,x) = n <;> simp only [shift,closeAt,he,if_true,if_false,hlt]
  | bound σ i => rfl
  | lam σ q =>
    simp only [shift,closeAt]
    rw [show d+amount+1 = d+1+amount by omega]
    exact congrArg (NTerm.lam σ) (term n (d+1) amount (cutoff+1) (Nat.succ_le_succ h) q)
  | bottom σ => rfl
  | ordinary f bs => simp only [shift,closeAt,args n d amount cutoff h bs]
  | numbered f τ k bs es =>
    simp only [shift,closeAt,args n d amount cutoff h bs,args n d amount cutoff h es]
  | auxApp σ τ q a =>
    simp only [shift,closeAt,term n d amount cutoff h q,term n d amount cutoff h a]
termination_by sizeOf q

theorem args (n : Name) (d amount cutoff : Nat) (h : cutoff ≤ d) (As : NArgs) :
    closeArgsAt n (d+amount) (shiftArgs amount cutoff As) =
      shiftArgs amount cutoff (closeArgsAt n d As) := by
  cases As with
  | nil => rfl
  | cons q qs =>
    simp only [closeArgsAt,shiftArgs,term n d amount cutoff h q,args n d amount cutoff h qs]
termination_by sizeOf As
end

theorem freshBody (n : Name) (d : Nat) (f : Head) (σ τ : Ty) (k : Nat) (bs es : NArgs) :
    closeAt n (d+1) (openNumbered f σ τ k bs es) =
      openNumbered f σ τ k (closeArgsAt n d bs) (closeArgsAt n d es) := by
  simp only [openNumbered,closeAt,NumberedWindowClosingOperationsProof.append,
    args n d 1 0 (Nat.zero_le d) bs,args n d 1 0 (Nat.zero_le d) es,closeArgsAt]

end LogicLineages.PersistentMarking.NumberedWindowClosingShiftProof
