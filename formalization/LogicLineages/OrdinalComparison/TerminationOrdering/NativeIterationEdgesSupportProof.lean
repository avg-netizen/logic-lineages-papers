module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeCarrierProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.RenamingEquivarianceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourceTypeSupport
open RecursiveComparison LiteralContexts NativeRecursor NativeCarrier NativeIterationEdges

theorem selectorProjection {Symbol : Type} {arity : Symbol → Nat} {Γ : List Ty} {η : Ty}
    (above : Symbol → Symbol → Prop) (P E : Term Symbol arity Γ η) :
    Weak Symbol arity above Γ ⟨η,embed (.app (.app (selector η) P) E)⟩ ⟨η,embed P⟩ := by
  apply Weak.put (.application η η) (.cons (embed (.app (selector η) P)) (.cons (embed E) .nil)) (embed P)
  apply Weak.select _ _ _ _ [η] (embed (.app (selector η) P)) _ (embed P) rfl
  · simp [argumentList]
  · simp only [embed,applyOriginalWith,selfArguments,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2]
    rfl
  · apply Weak.select _ _ _ _ [η,η] (embed (selector η)) _ (embed P) rfl
    · simp [argumentList]
    · rfl
    · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ η (embed P) (embed P)
      · simp [argumentList]
      · exact RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Γ η P

theorem stepProjection {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    (A : Ty) (P : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)))
    (i : Term Symbol arity [] indexType) : ConfinedWeak above (step A P i) P := by
  constructor
  · exact selectorProjection above P (constantTemplate (.arrow A A) i)
  · intro ρ hρ
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ hρ)))

theorem templateMonotonicity {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    (A : Ty) {Γ : List Ty} (i j : Term Symbol arity Γ indexType) (h : ConfinedStrict above i j) :
    ConfinedStrict above (constantTemplate A i) (constantTemplate A j) := by
  induction A generalizing Γ with
  | ground => exact h
  | arrow A D ihA ihD =>
      have hl := RenamingEquivarianceProof.renamedConfinedContextClosure Symbol arity above Γ
        (translatedType A::Γ) (translatedType A::Γ) indexType indexType
        (Renaming.weaken Γ (translatedType A)) .hole i j h
      have hb := ihD (i.rename (Renaming.weaken Γ (translatedType A)))
        (j.rename (Renaming.weaken Γ (translatedType A))) hl
      exact LiteralContextsProof.literalConfinedContextClosure Symbol arity above
        (translatedType A::Γ) Γ (translatedType D) (.arrow (translatedType A) (translatedType D))
        (.lam .hole) _ _ hb

theorem stepMonotonicity {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
    (A : Ty) (P : Term Symbol arity [] (.arrow (translatedType A) (translatedType A)))
    (i j : Term Symbol arity [] indexType) (h : ConfinedStrict above i j) :
    ConfinedStrict above (step A P i) (step A P j) := by
  exact LiteralContextsProof.literalConfinedContextClosure Symbol arity above [] [] _ _
    (.appArgument (.app (selector _) P) .hole) _ _ (templateMonotonicity above (.arrow A A) i j h)

theorem carrierMonotonicity {Symbol : Type} {arity : Symbol → Nat} {B : Ty}
    (above : Symbol → Symbol → Prop) (K L : Term Symbol arity [] (.arrow B B))
    (U : Term Symbol arity [] B) (h : ConfinedStrict above K L) :
    ConfinedStrict above (carrier K U) (carrier L U) := by
  have hs := RenamingEquivarianceProof.renamedConfinedContextClosure Symbol arity above [] [.ground] []
    (.arrow B B) (stepType B) (Renaming.weaken [] .ground) (.lam .hole) K L h
  exact LiteralContextsProof.literalConfinedContextClosure Symbol arity above [] [] (stepType B) B
    (.appFunction (.appArgument (.app (.recC B) .zeroC) .hole) U) _ _ hs

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeIterationEdgesSupportProof
