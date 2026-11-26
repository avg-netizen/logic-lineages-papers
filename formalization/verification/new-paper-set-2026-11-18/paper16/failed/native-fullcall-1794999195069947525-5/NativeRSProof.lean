import LogicLineages.PersistentMarking.NativeRSChainsProof
namespace LogicLineages.PersistentMarking.NativeRSProof
open Spine NativeReduction NativeTypingProof NativeRSFamiliesProof NativeRSContextProof NativeRSChainsProof TypeSupport

theorem appSupport (σ τ : Ty) (f a : Expr) (ρ : Ty) :
    ρ ∈ support (app σ τ f a) ↔ ρ ∈ subtypes τ ∨ ρ ∈ support f ∨ ρ ∈ support a := by
  simp only [app,support,supportArgs,List.mem_append,List.not_mem_nil,or_false]

theorem recSucc : NativeOrientationTargets.RecSucc := by
  intro S τ n A B hn hon hA hoA hB hoB
  have hf := familyTyping S τ n A B hn hA hB
  have hAn : PaperTerm S (app .ground (.arrow τ τ) A n) (.arrow τ τ) := appPaper S _ _ _ _ hA hn
  have hrec := recPaper S τ n A B hn hA hB
  have ht := appPaper S τ τ _ _ hAn hrec
  have hAty := SpineShiftProof.annotationExact _ _ _ hA.1
  have hnty := SpineShiftProof.annotationExact _ _ _ hn.1
  have hAnty := SpineShiftProof.annotationExact _ _ _ hAn.1
  have hrecty := SpineShiftProof.annotationExact _ _ _ hrec.1
  let extras := Args.cons (C1 τ n A B .ground) (.cons (C1 τ n A B (stepType τ)) (.cons (C1 τ n A B τ) .nil))
  have hwhole1 : Whole S (.recursor τ) .nil extras (.cons A (.cons n .nil)) := by
    apply Whole.cons
    · simpa only [hAty] using toStep S τ n A B hn hA hoA hB
    · apply Whole.cons
      · simpa only [hnty] using toNumber S τ n A B hn hon hA hB
      · exact .nil
  have hpre1 : Precedes S (.recursor τ) (.app .ground (.arrow τ τ)) := ⟨1,0,rfl,rfl,by decide⟩
  have hfirst : Weak S (C0 τ n A B (.arrow τ τ)) (app .ground (.arrow τ τ) A n) :=
    .copy (hf.c0 (.arrow τ τ)) hAn hpre1 hwhole1
  have hwhole2 : Whole S (.recursor τ) .nil extras
      (.cons (app .ground (.arrow τ τ) A n) (.cons (recTerm τ n A B) .nil)) := by
    apply Whole.cons
    · simpa only [hAnty] using hfirst
    · apply Whole.cons
      · simpa only [hrecty] using toRecursion S τ n A B hn hon hA hoA hB hoB
      · exact .nil
  have hpre2 : Precedes S (.recursor τ) (.app τ τ) := ⟨1,0,rfl,rfl,by decide⟩
  have hroot : Weak S (C0 τ n A B τ) (app τ τ (app .ground (.arrow τ τ) A n) (recTerm τ n A B)) :=
    .copy (hf.c0 τ) ht hpre2 hwhole2
  have hw := prefixSelections S τ n A B _ hn hA hB ht hroot
  have hs := recPaper S τ (succ n) A B (succPaper S n hn) hA hB
  have hos := recOrdinary τ (succ n) A B ⟨True.intro,hon,True.intro⟩ hoA hoB
  have hot := appOrdinary τ τ _ _ (appOrdinary .ground (.arrow τ τ) A n hoA hon) (recOrdinary τ n A B hon hoA hoB)
  refine ⟨⟨τ,hs,ht,hos,hot⟩,Strict.intro hs ht rfl hw,?_⟩
  have hsmallRec := (recPredecessor S τ n A B hn hon hA hoA hB hoB).2.2
  have hsmallAn : Included (app .ground (.arrow τ τ) A n) (recTerm τ (succ n) A B) := by
    intro ρ h
    rw [appSupport] at h
    rcases h with h | h | h
    · exact leftIncluded τ τ _ B ρ (TypeSupportFoundationProof.rootSupport (rec2 τ (succ n) A) ρ h)
    · exact leftIncluded τ τ _ B ρ (rightIncluded (stepType τ) (.arrow τ τ) _ A ρ h)
    · exact leftIncluded τ τ _ B ρ (leftIncluded (stepType τ) (.arrow τ τ) _ A ρ
        (rightIncluded .ground (.arrow (stepType τ) (.arrow τ τ)) _ (succ n) ρ
          (rightIncluded .ground .ground _ n ρ h)))
  intro ρ h
  rw [appSupport] at h
  rcases h with h | h | h
  · exact TypeSupportFoundationProof.rootSupport (recTerm τ (succ n) A B) ρ h
  · exact hsmallAn ρ h
  · exact hsmallRec ρ h
end LogicLineages.PersistentMarking.NativeRSProof
