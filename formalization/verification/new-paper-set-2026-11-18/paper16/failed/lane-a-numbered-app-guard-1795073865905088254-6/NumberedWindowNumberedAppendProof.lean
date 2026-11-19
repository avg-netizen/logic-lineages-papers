import LogicLineages.PersistentMarking.NumberedWindowNumberedDomainProof
import LogicLineages.PersistentMarking.NumberedWindowApplicationPathProof
import LogicLineages.PersistentMarking.NumberedWindowBindingChecks

namespace LogicLineages.PersistentMarking.NumberedWindowNumberedAppendProof
open Spine NumberedWindowSyntax NumberedWindowDomain NumberedWindowRules NumberedWindowApplicationTargets
open NumberedWindowApplicationDomainProof NumberedWindowApplicationPathProof
open NumberedWindowNumberedDomainProof

theorem appendNil (es : NArgs) : es.append .nil = es := by
  cases es with
  | nil => rfl
  | cons a tail => simp only [NArgs.append,appendNil tail]
termination_by sizeOf es

theorem appendOneCons (es : NArgs) (a : NTerm) (As : NArgs) :
    (es.append (.cons a .nil)).append As = es.append (.cons a As) := by
  cases es with
  | nil => rfl
  | cons e tail => simp only [NArgs.append,appendOneCons tail a As]
termination_by sizeOf es

theorem one {S : Signature} {K : List Ty} {C : BoundContext}
    {f : Head} {σ τ : Ty} {k : Nat} {bs es : NArgs} {A : NTerm}
    (hk : DecisionSourceUniverse.Closed K)
    (hOwn : InWindow S K C (.arrow σ τ) (.numbered f (.arrow σ τ) (k+1) bs es))
    (hA : InWindow S K C σ A) :
    WindowPath S K C τ (.auxApp σ τ (.numbered f (.arrow σ τ) (k+1) bs es) A)
      (.numbered f τ k bs (es.append (.cons A .nil))) := by
  have hOpen := openNumberedWindow S K C f σ τ k bs es hk hOwn
  have hAppend := appendArg S K C f σ τ k bs es A hk hOwn hA
  have hBeta : RawStep S K (.auxApp σ τ (.lam σ (openNumbered f σ τ k bs es)) A)
      (.numbered f τ k bs (es.append (.cons A .nil))) := by
    rw [← NumberedWindowBindingChecks.exact_OpenNumberedBeta f σ τ k bs es A]
    exact .beta
  exact .next ⟨.auxFunction .fabs,app S K C σ τ _ A hk hOwn hA,
    app S K C σ τ _ A hk hOpen hA⟩
    (single ⟨hBeta,app S K C σ τ _ A hk hOpen hA,hAppend⟩)

theorem wholeNumbered : WholeNumberedAppend := by
  intro S K C ds τ f k bs es As hk hOwn hAs
  induction hAs generalizing k es with
  | nil =>
    refine ⟨_,rfl,?_⟩
    rw [appendNil]
    exact .refl hOwn
  | @cons σ A tail Tail hA ht ih =>
    have hShape : InWindow S K C (.arrow σ (ArrowPrefix tail τ))
        (.numbered f (.arrow σ (ArrowPrefix tail τ)) ((k+tail.length)+1) bs es) := by
      simpa only [ArrowPrefix,List.length_cons,Nat.add_assoc] using hOwn
    have hOne := one hk hShape hA
    obtain ⟨start,mid,hStart,hMid,hPrefix⟩ := lift S K C tail τ _ _ Tail hk hOne ht
    have hNext := (endpoints hOne).2
    obtain ⟨mid',hMid',hSuffix⟩ := ih (k := k) (es := es.append (.cons A .nil)) hNext
    have hSame : mid = mid' := Option.some.inj (hMid.symm.trans hMid')
    subst mid'
    refine ⟨start,?_,?_⟩
    · exact (appEq hShape.1 hA.1 Tail).trans hStart
    · rw [← appendOneCons es A Tail]
      exact trans hPrefix hSuffix

end LogicLineages.PersistentMarking.NumberedWindowNumberedAppendProof
