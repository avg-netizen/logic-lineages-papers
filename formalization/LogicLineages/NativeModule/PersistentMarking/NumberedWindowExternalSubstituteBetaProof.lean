module

public import LogicLineages.NativeModule.PersistentMarking.NumberedWindowExternalSubstituteShiftProof

@[expose] public section

namespace LogicLineages.PersistentMarking.NumberedWindowExternalSubstituteBetaProof
open NumberedWindowSyntax NumberedWindowBindingBaseProof NumberedWindowExternalBindingNaturalityTargets

private theorem bound (vs : NArgs) (d k : Nat) (a : NTerm) (σ : Ty) (i : Nat) :
    substitute vs (d+k) (substitute (.cons a .nil) k (.bound σ i)) =
      substitute (.cons (substitute vs d a) .nil) k (substitute vs (d+k+1) (.bound σ i)) := by
  by_cases lo : i < k
  · have h1 : i < d+k := by omega
    have h2 : i < d+k+1 := by omega
    simp [substitute,lo,h1,h2]
  · by_cases hit : i = k
    · subst i
      have h2 : k < d+k+1 := by omega
      simp only [substitute,h2,if_true,lo,if_false,Nat.sub_self,NArgs.get]
      exact NumberedWindowExternalSubstituteShiftProof.term vs d k 0 (Nat.zero_le d) a
    · have away : i-k ≠ 0 := by omega
      have nonzero := singletonPast a _ away
      by_cases before : i < d+k+1
      · have h1 : i-1 < d+k := by omega
        simp only [substitute,lo,if_false,nonzero,NArgs.length,before,if_true,h1,
          singletonPast (substitute vs d a) _ away]
      · have h1 : ¬ i-1 < d+k := by omega
        have idx : i-1-(d+k) = i-(d+k+1) := by omega
        cases h : vs.get (i-(d+k+1)) with
        | some z =>
          simp only [substitute,lo,if_false,nonzero,NArgs.length,before,h1,idx,h]
          simpa only [Nat.add_zero] using
            (NumberedWindowExternalShiftGapProof.remove z (substitute vs d a) k (d+k) 0 (by omega)).symm
        | none =>
          have len := getNoneLength vs _ h
          have hlate : ¬ i-vs.length < k := by omega
          have hNZ : i-vs.length-k ≠ 0 := by omega
          simp only [substitute,lo,if_false,nonzero,NArgs.length,before,h1,idx,h,hlate,
            singletonPast (substitute vs d a) _ hNZ]
          congr 1 <;> omega

mutual
theorem term (vs : NArgs) (d k : Nat) (a q : NTerm) :
    substitute vs (d+k) (substitute (.cons a .nil) k q) =
      substitute (.cons (substitute vs d a) .nil) k (substitute vs (d+k+1) q) := by
  cases q with
  | free | bottom => rfl
  | bound σ i => exact bound vs d k a σ i
  | lam σ q =>
    simpa only [substitute,Nat.add_assoc] using congrArg (NTerm.lam σ) (term vs d (k+1) a q)
  | ordinary f bs => simp only [substitute,args vs d k a bs]
  | numbered f τ n bs es => simp only [substitute,args vs d k a bs,args vs d k a es]
  | auxApp σ τ q b => simp only [substitute,term vs d k a q,term vs d k a b]
termination_by sizeOf q
theorem args (vs : NArgs) (d k : Nat) (a : NTerm) (xs : NArgs) :
    substituteArgs vs (d+k) (substituteArgs (.cons a .nil) k xs) =
      substituteArgs (.cons (substitute vs d a) .nil) k (substituteArgs vs (d+k+1) xs) := by
  cases xs with
  | nil => rfl
  | cons q qs => simp only [substituteArgs,term vs d k a q,args vs d k a qs]
termination_by sizeOf xs
end

theorem beta : SubstituteBeta := by
  intro vs d a body
  exact term vs d 0 a body

end LogicLineages.PersistentMarking.NumberedWindowExternalSubstituteBetaProof
