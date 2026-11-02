module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorSupportProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open RecursiveComparison LiteralContexts NativeRecursor
variable {Symbol : Type} {arity : Symbol → Nat} (above : Symbol → Symbol → Prop)
variable {Γ : List Ty} {τ : Ty} (n : Term Symbol arity Γ .ground)
variable (A : Term Symbol arity Γ (stepType τ)) (B : Term Symbol arity Γ τ)

theorem successorStrict : Strict Symbol arity above Γ
    ⟨.ground,embed (.app .succC n)⟩ ⟨.ground,embed n⟩ := by
  apply Strict.mark _ _ _ rfl
  apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ [] .nil .ground (embed n) (embed n)
  · simp [argumentList]
  · exact RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Γ .ground n

theorem outerPrefixes (t : MarkedTerm Symbol arity Γ τ)
    (h : Weak Symbol arity above Γ ⟨τ,C0 n A B τ⟩ ⟨τ,t⟩) :
    Weak Symbol arity above Γ ⟨τ,P n A B τ⟩ ⟨τ,t⟩ := by
  apply Weak.select _ _ _ _ [τ]
    (embed (.app (.app (.recC τ) (.app .succC n)) A)) (C2 n A B τ) t rfl
  · simp [P,argumentList]
  · simp only [embed,applyOriginalWith,selfArguments,
      Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2]
    rfl
  · apply Weak.select _ _ _ _ [stepType τ,τ]
      (embed (.app (.recC τ) (.app .succC n))) (C1 n A B τ) t rfl
    · simp [C2,argumentList]
    · simp only [embed,applyOriginalWith,selfArguments,
        Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2]
      rfl
    · apply Weak.select _ _ _ _ [.ground,stepType τ,τ]
        (embed (.recC τ)) (C0 n A B τ) t rfl
      · exact List.mem_append.mpr (Or.inl List.mem_cons_self)
      · rfl
      · exact h

theorem extraChain {ρ : Ty} (t : MarkedTerm Symbol arity Γ ρ)
    (h : Weak Symbol arity above Γ ⟨ρ,P n A B ρ⟩ ⟨ρ,t⟩)
    (he : ρ=τ) : Weak Symbol arity above Γ ⟨ρ,C0 n A B ρ⟩ ⟨ρ,t⟩ := by
  subst ρ
  apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ τ (C1 n A B τ) t
  · simp [C0,argumentList]
  · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ τ (C2 n A B τ) t
    · simp [C1,argumentList]
    · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ τ (P n A B τ) t
      · simp [C2,argumentList]
      · exact h

theorem stepArgument : Weak Symbol arity above Γ ⟨stepType τ,C0 n A B (stepType τ)⟩ ⟨stepType τ,embed A⟩ := by
  apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ _ (C1 n A B (stepType τ)) (embed A)
  · simp [C0,argumentList]
  · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ _ (C2 n A B (stepType τ)) (embed A)
    · simp [C1,argumentList]
    · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ _ (embed A) (embed A)
      · simp [C2,argumentList]
      · exact RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Γ _ A

theorem predecessorArgument : Weak Symbol arity above Γ ⟨.ground,C0 n A B .ground⟩ ⟨.ground,embed n⟩ := by
  apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ _ (C1 n A B .ground) (embed n)
  · simp [C0,argumentList]
  · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ _ (embed (.app .succC n)) (embed n)
    · simp [C1,argumentList]
    · exact RecursiveComparisonProof.strictWeakInclusion Symbol arity above Γ _ _ (successorStrict above n)

theorem recursiveArgument : Weak Symbol arity above Γ ⟨τ,C0 n A B τ⟩ ⟨τ,embed (recursorTerm n A B)⟩ := by
  apply extraChain above n A B _ _ rfl
  have hs := LiteralContextsProof.literalContextStrictClosure Symbol arity above Γ Γ .ground τ
    (.appFunction (.appFunction (.appArgument (.recC τ) .hole) A) B)
    (.app .succC n) n (successorStrict above n)
  cases hs with
  | mark s r t hm hw =>
      have he : P n A B τ = r := Option.some.inj hm
      subst r
      exact hw

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorSupportProof
