module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeBetaCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NativeRecursorProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionProof
open Source LiteralContexts OriginalReductionBindingProof

theorem rootOrientation : OriginalReductionTargets.RootOrientation := by
  intro Symbol arity above Γ τ s t h
  cases h with
  | beta body arg => exact NativeBetaCasesProof.betaConfinedOrientation Symbol arity above Γ _ τ body arg
  | caseZero A B => exact NativeBetaCasesProof.caseFirstConfinedOrientation Symbol arity above Γ τ .zeroC _ _
  | caseSucc n A B => exact NativeBetaCasesProof.caseSecondConfinedOrientation Symbol arity above Γ τ (.app .succC n) _ _
  | recZero A B => exact NativeRecursorProof.zeroConfinedOrientation Symbol arity above Γ τ _ _
  | recSucc n A B => exact NativeRecursorProof.successorConfinedOrientation Symbol arity above Γ τ n A B

theorem contextualOrientation : OriginalReductionTargets.ContextualOrientation := by
  intro Symbol arity above Γ τ s t h
  induction h with
  | root h => exact rootOrientation Symbol arity above _ _ _ _ h
  | appFunction a h ih =>
      exact LiteralContextsProof.literalConfinedContextClosure Symbol arity above _ _ _ _ (.appFunction .hole a) _ _ ih
  | appArgument f h ih =>
      exact LiteralContextsProof.literalConfinedContextClosure Symbol arity above _ _ _ _ (.appArgument f .hole) _ _ ih
  | abstraction h ih =>
      exact LiteralContextsProof.literalConfinedContextClosure Symbol arity above _ _ _ _ (.lam .hole) _ _ ih
  | rankedArgument hd as bs i h he ih =>
      have hc := LiteralContextsProof.literalConfinedContextClosure Symbol arity above _ _ .ground .ground
        (.ranked hd i as .hole) (as i) (bs i) ih
      have ha : plug (.ranked hd i as .hole) (as i)=Term.ranked hd as := by
        apply congrArg (Term.ranked hd)
        funext j
        by_cases hj : j=i
        · subst j; simp [plug]
        · simp [plug,hj]
      have hb : plug (.ranked hd i as .hole) (bs i)=Term.ranked hd bs := by
        apply congrArg (Term.ranked hd)
        funext j
        by_cases hj : j=i
        · subst j; simp [plug]
        · simp [plug,hj,he j hj]
      rw [ha,hb] at hc
      exact hc

theorem rootSubstitutionClosure : OriginalReductionTargets.RootSubstitutionClosure := by
  intro Symbol arity Γ Δ τ s t θ h
  cases h with
  | beta body arg =>
      change RootReduction Symbol arity (.app (.lam (body.substitute θ.lift)) (arg.substitute θ))
        ((body.substitute (Substitution.single arg)).substitute θ)
      rw [←betaSubstitutionFusion body arg θ]
      exact .beta _ _
  | caseZero A B => exact .caseZero _ _
  | caseSucc n A B => exact .caseSucc (n.substitute θ) _ _
  | recZero A B => exact .recZero _ _
  | recSucc n A B => exact .recSucc (n.substitute θ) (A.substitute θ) (B.substitute θ)

theorem contextualSubstitutionClosure : OriginalReductionTargets.ContextualSubstitutionClosure := by
  intro Symbol arity Γ Δ τ s t θ h
  induction h generalizing Δ with
  | root h => exact .root (rootSubstitutionClosure Symbol arity _ Δ _ _ _ θ h)
  | appFunction a h ih => exact .appFunction (a.substitute θ) (ih Δ θ)
  | appArgument f h ih => exact .appArgument (f.substitute θ) (ih Δ θ)
  | abstraction h ih => exact .abstraction (ih _ θ.lift)
  | rankedArgument hd as bs i h he ih =>
      exact .rankedArgument hd (fun j => (as j).substitute θ) (fun j => (bs j).substitute θ) i
        (ih Δ θ) (fun j hj => congrArg (fun q => q.substitute θ) (he j hj))

theorem substitutedContextualOrientation : OriginalReductionTargets.SubstitutedContextualOrientation := by
  intro Symbol arity above Γ Δ τ s t θ h
  exact contextualOrientation Symbol arity above Δ τ (s.substitute θ) (t.substitute θ)
    (contextualSubstitutionClosure Symbol arity Γ Δ τ s t θ h)

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalReductionProof
