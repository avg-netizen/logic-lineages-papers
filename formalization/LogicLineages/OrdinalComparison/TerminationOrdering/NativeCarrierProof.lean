module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourceTypeSupport
open RecursiveComparison LiteralContexts NativeRecursor NativeCarrier NativeCarrierSupportProof

private theorem nativeFunction {Symbol : Type} {arity : Symbol → Nat} {B : Ty}
    (above : Symbol → Symbol → Prop) (P K : Term Symbol arity [] (.arrow B B))
    (U : Term Symbol arity [] B)
    (h : Weak Symbol arity above [] ⟨.arrow B B,embed K⟩ ⟨.arrow B B,embed P⟩) :
    Weak Symbol arity above [] ⟨.arrow B B,native K U (.arrow B B)⟩ ⟨.arrow B B,embed P⟩ := by
  apply Weak.select _ _ _ _ [.ground] (inner K U (stepType B)) _ (embed P) rfl
  · simp [native,argumentList]
  · simp only [inner,applyOriginalWith,selfArguments,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2,appendArguments]
    rfl
  · apply Weak.select _ _ _ _ [.ground] (middle K U (stepType B)) _ (embed P) rfl
    · simp [argumentList]
    · simp only [middle,applyOriginalWith,selfArguments,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2,appendArguments]
      rfl
    · apply Weak.select _ _ _ _ [.ground] (embed (unusedGroundStep K)) (embed K) (embed P) rfl
      · simp [argumentList]
      · exact unusedConsumption K _
      · exact h

theorem baseStrict : NativeCarrierTargets.BaseStrict := by
  intro Symbol arity above B K U
  exact NativeRecursorProof.zeroConfinedOrientation Symbol arity above [] B (unusedGroundStep K) U

theorem applicationClosure : NativeCarrierTargets.ApplicationClosure := by
  intro Symbol arity above B P K U T hKP hWT
  constructor
  · apply Strict.mark _ (outer K U B) _ rfl
    apply outerPrefixes K U above
    apply Weak.copy (.recursor B) (.application B B) .nil
      [.ground,stepType B,B]
      (.cons (inner K U .ground) (.cons (inner K U (stepType B)) (.cons (inner K U B) .nil)))
      (.cons (embed P) (.cons (embed T) .nil)) True.intro
    intro p hp
    simp only [argumentList,List.mem_cons,List.not_mem_nil,or_false] at hp
    rcases hp with rfl | rfl
    · exact nativeFunction above P K U hKP.1
    · apply extraChain K U above
      have hw := hWT.1
      cases hw with
      | mark s r t hm hw =>
          have he : outer K U B=r := Option.some.inj hm
          subst r
          exact hw
  · have hk : typeSupport K ⊆ typeSupport (carrier K U) := by
      intro ρ hρ
      have hr := (Source.SourceTypeSupportProof.supportDepthRenaming Symbol arity [] [.ground]
        (.arrow B B) K (Renaming.weaken [] .ground)).1
      have hb : ρ ∈ typeSupport (K.rename (Renaming.weaken [] .ground)) := hr.symm ▸ hρ
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_union_right _ (Finset.mem_union_right _ hb))))
    intro ρ hρ
    change ρ ∈ B.subtypes.toFinset ∪ (typeSupport P ∪ typeSupport T) at hρ
    rcases Finset.mem_union.mp hρ with hroot | hargs
    · exact Finset.mem_union_left _ hroot
    rcases Finset.mem_union.mp hargs with hp | ht
    · exact hk (hKP.2 hp)
    · exact hWT.2 ht

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierProof
