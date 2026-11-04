module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootProof
open Source NumberedRewriteSyntax NumberedWindowReduction

def LambdaCases {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} {tau : Ty}
    (q r : AuxTerm Symbol arity Gamma tau) : Prop :=
  match q, r with
  | .lam (sigma := sigma) (tau := upsilon) body, r =>
      r = .bottom (.arrow sigma upsilon) ∨
      ∃ body' : AuxTerm Symbol arity (sigma::Gamma) upsilon,
        WindowStep Symbol arity symbols S above (sigma::Gamma) upsilon body body' ∧ r = .lam body'
  | _, _ => True

theorem lambdaCasesOfStep {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {q r : AuxTerm Symbol arity Gamma tau} (h : WindowStep Symbol arity symbols S above Gamma tau q r) :
    LambdaCases symbols S above q r := by
  induction h using WindowStep.rec (motive_2 := fun _ _ _ _ _ => True)
  case lam body body' h ih => exact Or.inr ⟨body',h,rfl⟩
  case bottom q hn => cases q <;> first | exact Or.inl rfl | trivial
  all_goals trivial

theorem actualLambdaStepCases : NumberedLambdaRootTargets.ActualLambdaStepCases := by
  intro Symbol arity symbols S above Gamma sigma tau body q
  constructor
  · intro h
    exact lambdaCasesOfStep h
  · intro h
    rcases h with h | ⟨body',hs,hq⟩
    · subst q
      exact WindowStep.bottom (.lam body) (by intro he; cases he)
    · subst q
      exact WindowStep.lam body body' hs

theorem actualBetaApplicationStepCases : NumberedLambdaRootTargets.ActualBetaApplicationStepCases := by
  intro Symbol arity symbols S above Gamma sigma tau body a q
  constructor
  · intro h
    cases h with
    | appFunction f g a h =>
      rcases (actualLambdaStepCases Symbol arity symbols S above Gamma sigma tau body g).mp h with hg | ⟨body',hs,hg⟩
      · subst g
        exact Or.inr (Or.inr (Or.inl rfl))
      · subst g
        exact Or.inr (Or.inr (Or.inr ⟨body',hs,rfl⟩))
    | beta body a => exact Or.inr (Or.inl rfl)
    | bottom q h => exact Or.inl rfl
  · intro h
    rcases h with h | h | h | ⟨body',hs,h⟩
    · subst q
      exact WindowStep.bottom (.app (.lam body) a) (by intro he; cases he)
    · subst q
      exact WindowStep.beta body a
    · subst q
      exact WindowStep.appFunction (.lam body) (.bottom (.arrow sigma tau)) a
        (WindowStep.bottom (.lam body) (by intro he; cases he))
    · subst q
      exact WindowStep.appFunction (.lam body) (.lam body') a (WindowStep.lam body body' hs)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedLambdaRootProof
