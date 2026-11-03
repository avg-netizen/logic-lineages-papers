module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorProof
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison LiteralContexts NativeRecursor

theorem zeroConfinedOrientation : NativeRecursorTargets.ZeroConfinedOrientation := by
  intro Symbol arity above Γ τ A B
  constructor
  · apply Strict.mark _ _ _ rfl
    apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ [] .nil τ (embed B) (embed B)
    · simp [recursorTerm,embed,argumentList]
    · exact RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Γ τ B
  · intro ρ hρ
    simp only [recursorTerm,typeSupport,Finset.mem_union] at hρ ⊢
    tauto

theorem successorConfinedOrientation : NativeRecursorTargets.SuccessorConfinedOrientation := by
  intro Symbol arity above Γ τ n A B
  constructor
  · apply Strict.mark _ (P n A B τ) _ rfl
    apply NativeRecursorSupportProof.outerPrefixes above n A B
    apply Weak.copy (.recursor τ) (.application τ τ) .nil
      [.ground,stepType τ,τ]
      (.cons (C1 n A B .ground) (.cons (C1 n A B (stepType τ)) (.cons (C1 n A B τ) .nil)))
      (.cons (embed (.app A n)) (.cons (embed (recursorTerm n A B)) .nil)) True.intro
    intro p hp
    simp only [argumentList,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · apply Weak.copy (.recursor τ) (.application .ground (.arrow τ τ)) .nil
        [.ground,stepType τ,τ]
        (.cons (C1 n A B .ground) (.cons (C1 n A B (stepType τ)) (.cons (C1 n A B τ) .nil)))
        (.cons (embed A) (.cons (embed n) .nil)) True.intro
      intro p hp
      simp only [argumentList,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with rfl | rfl
      · exact NativeRecursorSupportProof.stepArgument above n A B
      · exact NativeRecursorSupportProof.predecessorArgument above n A B
    · exact NativeRecursorSupportProof.recursiveArgument above n A B
  · have hn : typeSupport n ⊆ typeSupport (.app .succC n) := by
      intro ρ hρ
      exact Finset.mem_union_right _ (Finset.mem_union_right _ hρ)
    have hr := LiteralContextsProof.literalContextSupportMonotonicity Symbol arity Γ Γ .ground τ
      (.appFunction (.appFunction (.appArgument (.recC τ) .hole) A) B)
      (.app .succC n) n hn
    intro ρ hρ
    change ρ ∈ τ.subtypes.toFinset ∪ (typeSupport (.app A n) ∪ typeSupport (recursorTerm n A B)) at hρ
    rcases Finset.mem_union.mp hρ with hroot | hrest
    · exact Finset.mem_union_left _ hroot
    rcases Finset.mem_union.mp hrest with happ | hrec
    · change ρ ∈ (Ty.arrow τ τ).subtypes.toFinset ∪ (typeSupport A ∪ typeSupport n) at happ
      rcases Finset.mem_union.mp happ with hroot | hargs
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_left _ hroot))
      rcases Finset.mem_union.mp hargs with ha | hn'
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_union_right _ ha)))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_union_right _ (hn hn'))))))
    · exact hr hrec

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorProof
