module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication Source.SourceTypeSupport
open RecursiveComparison LiteralContexts NativeBetaCases NativeBetaCasesSupportProof

theorem betaConfinedOrientation : NativeBetaCasesTargets.BetaConfinedOrientation := by
  intro Symbol arity above Γ σ τ body arg
  constructor
  · let base : Arguments Symbol arity Γ (headArguments arity (.application σ τ)) :=
      .cons (embed (.lam body)) (.cons (embed arg) .nil)
    let self : MarkedTerm Symbol arity Γ σ := .marked (.application σ τ) σ base [] .nil
    have hs : Weak Symbol arity above Γ ⟨σ,self⟩ ⟨σ,embed arg⟩ :=
      LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ (.application σ τ) base [] .nil σ (embed arg) (embed arg)
        (by simp [base,argumentList]) (RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Γ σ arg)
    have hg := OrdinaryTemplateGraftingProof.distinguishedVariableGrafting Symbol arity above Γ σ τ body self (embed arg) hs
    rw [betaEmbedding body arg] at hg
    apply Strict.mark _ (.marked (.application σ τ) τ base [] .nil) _ rfl
    apply Weak.select (.application σ τ) base [] .nil [σ] (embed (.lam body))
      (substituteTerm (embed body) (extendEnvironment (fun v => .var v) self))
      (embed (body.substitute (Substitution.single arg))) rfl
    · simp [base,argumentList]
    · exact originalBetaApplication body self
    · exact hg
  · exact betaSupport body arg

theorem caseFirstConfinedOrientation : NativeBetaCasesTargets.CaseFirstConfinedOrientation := by
  intro Symbol arity above Γ τ u A B
  constructor
  · apply Strict.mark _ _ _ rfl
    apply Weak.select _ _ _ _ [τ] (embed (.app (.app (.caseC τ) u) A)) _ (embed A) rfl
    · simp [argumentList]
    · simp only [embed,applyOriginalWith,selfArguments,Source.SourceMarkedBindingProof.markedSubstitutionIdentity.2]
      rfl
    · apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ _ _ τ (embed A) (embed A)
      · simp [argumentList]
      · exact RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Γ τ A
  · intro ρ hρ
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_right _ hρ)))

theorem caseSecondConfinedOrientation : NativeBetaCasesTargets.CaseSecondConfinedOrientation := by
  intro Symbol arity above Γ τ u A B
  constructor
  · apply Strict.mark _ _ _ rfl
    apply LiteralContextsProof.actualZeroArgumentSelect Symbol arity above Γ _ _ [] .nil τ (embed B) (embed B)
    · simp [argumentList]
    · exact RecursiveComparisonProof.literalOrdinaryReflexivity Symbol arity above Γ τ B
  · intro ρ hρ
    exact Finset.mem_union_right _ (Finset.mem_union_right _ hρ)

end LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesProof
