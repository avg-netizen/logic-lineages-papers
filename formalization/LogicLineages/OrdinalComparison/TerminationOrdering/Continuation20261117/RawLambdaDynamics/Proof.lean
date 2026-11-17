module
public import LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Targets
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Proof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

def LambdaStepCases {Symbol : Type} {arity : Symbol → Nat}
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} {tau : Ty}
    (source target : AuxTerm Symbol arity Gamma tau) : Prop :=
  match source, target with
  | .lam (sigma := sigma) (tau := upsilon) body, target =>
      target = .bottom (.arrow sigma upsilon) ∨
        ∃ next : AuxTerm Symbol arity (sigma :: Gamma) upsilon,
          RawStep Symbol arity above (sigma :: Gamma) upsilon body next ∧
          target = .lam next
  | _, _ => True

theorem lambdaStepCasesOfStep {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {source target : AuxTerm Symbol arity Gamma tau}
    (h : RawStep Symbol arity above Gamma tau source target) :
    LambdaStepCases above source target := by
  induction h using RawStep.rec (motive_2 := fun _ _ _ _ _ => True)
  case lam body next h ih => exact Or.inr ⟨next, h, rfl⟩
  case bottom source hn => cases source <;> first | exact Or.inl rfl | trivial
  all_goals trivial

theorem lambdaStepCases {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {body : AuxTerm Symbol arity (sigma :: Gamma) tau}
    {target : AuxTerm Symbol arity Gamma (.arrow sigma tau)}
    (h : RawStep Symbol arity above Gamma (.arrow sigma tau) (.lam body) target) :
    target = .bottom (.arrow sigma tau) ∨
      ∃ next : AuxTerm Symbol arity (sigma :: Gamma) tau,
        RawStep Symbol arity above (sigma :: Gamma) tau body next ∧
        target = .lam next :=
  lambdaStepCasesOfStep h

theorem bottomStepTerminal {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {target : AuxTerm Symbol arity Gamma tau}
    (h : RawStep Symbol arity above Gamma tau (.bottom tau) target) : False := by
  cases h with
  | bottom source hn => exact hn rfl

theorem bottomPathTerminal {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {target : AuxTerm Symbol arity Gamma tau}
    (h : RawSteps Symbol arity above Gamma tau (.bottom tau) target) :
    target = .bottom tau := by
  cases h with
  | refl => rfl
  | next source next target hstep hrest =>
      exact False.elim (bottomStepTerminal hstep)

def LambdaPathCases {Symbol : Type} {arity : Symbol → Nat}
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} {tau : Ty}
    (source target : AuxTerm Symbol arity Gamma tau) : Prop :=
  match source, target with
  | .lam (sigma := sigma) (tau := upsilon) body, target =>
      target = .bottom (.arrow sigma upsilon) ∨
        ∃ next : AuxTerm Symbol arity (sigma :: Gamma) upsilon,
          RawSteps Symbol arity above (sigma :: Gamma) upsilon body next ∧
          target = .lam next
  | _, _ => True

theorem lambdaPathCasesOfPath {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {source target : AuxTerm Symbol arity Gamma tau}
    (h : RawSteps Symbol arity above Gamma tau source target) :
    LambdaPathCases above source target := by
  induction h with
  | refl source =>
      cases source with
      | lam body => exact Or.inr ⟨body, .refl body, rfl⟩
      | _ => trivial
  | next source next target hstep hrest ih =>
      cases source with
      | lam body =>
          rcases lambdaStepCases hstep with hbottom | ⟨child, hchild, hnext⟩
          · subst next
            exact Or.inl (bottomPathTerminal hrest)
          · subst next
            rcases ih with hbottom | ⟨last, hpath, htarget⟩
            · exact Or.inl hbottom
            · exact Or.inr ⟨last, .next body child last hchild hpath, htarget⟩
      | _ => trivial

theorem liftLambdaPath {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {body next : AuxTerm Symbol arity (sigma :: Gamma) tau}
    (h : RawSteps Symbol arity above (sigma :: Gamma) tau body next) :
    RawSteps Symbol arity above Gamma (.arrow sigma tau) (.lam body) (.lam next) := by
  induction h with
  | refl body => exact .refl (.lam body)
  | next body next last hstep hrest ih =>
      exact .next (.lam body) (.lam next) (.lam last) (.lam body next hstep) ih

theorem actualRawLambdaPathFactorization : Targets.ActualRawLambdaPathFactorization := by
  intro Symbol arity above Gamma sigma tau body target
  constructor
  · intro h
    exact lambdaPathCasesOfPath h
  · rintro (hbottom | ⟨next, hpath, htarget⟩)
    · subst target
      exact .next _ _ _ (.bottom (.lam body) (by intro he; cases he)) (.refl _)
    · subst target
      exact liftLambdaPath hpath

theorem bottomAccessible {Symbol : Type} {arity : Symbol → Nat}
    (above : Symbol → Symbol → Prop) (Gamma : List Ty) (tau : Ty) :
    Acc (fun successor source => RawStep Symbol arity above Gamma tau source successor)
      (.bottom tau) := by
  refine Acc.intro _ ?_
  intro target h
  exact False.elim (bottomStepTerminal h)

theorem lambdaAccessibleOfBodyAccessible {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {body : AuxTerm Symbol arity (sigma :: Gamma) tau}
    (h : Acc (fun successor source =>
      RawStep Symbol arity above (sigma :: Gamma) tau source successor) body) :
    Acc (fun successor source =>
      RawStep Symbol arity above Gamma (.arrow sigma tau) source successor) (.lam body) := by
  induction h with
  | intro body hbody ih =>
      refine Acc.intro (AuxTerm.lam body) ?_
      intro target hstep
      rcases lambdaStepCases hstep with hbottom | ⟨next, hnext, htarget⟩
      · subst target
        exact bottomAccessible above Gamma (.arrow sigma tau)
      · subst target
        exact ih next hnext

theorem bodyAccessibleOfLambdaAccessible {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {body : AuxTerm Symbol arity (sigma :: Gamma) tau}
    (h : Acc (fun successor source =>
      RawStep Symbol arity above Gamma (.arrow sigma tau) source successor) (.lam body)) :
    Acc (fun successor source =>
      RawStep Symbol arity above (sigma :: Gamma) tau source successor) body := by
  have reflect : ∀ (source : AuxTerm Symbol arity Gamma (.arrow sigma tau)),
      Acc (fun successor source =>
        RawStep Symbol arity above Gamma (.arrow sigma tau) source successor) source →
      ∀ (child : AuxTerm Symbol arity (sigma :: Gamma) tau), source = .lam child →
        Acc (fun successor source =>
          RawStep Symbol arity above (sigma :: Gamma) tau source successor) child := by
    intro source hs
    induction hs with
    | intro source hs ih =>
        intro child hsource
        subst source
        refine Acc.intro child ?_
        intro next hnext
        exact ih (.lam next) (.lam child next hnext) next rfl
  exact reflect (.lam body) h body rfl

theorem actualRawLambdaAccessibilityEquivalence :
    Targets.ActualRawLambdaAccessibilityEquivalence := by
  intro Symbol arity above Gamma sigma tau body
  exact ⟨bodyAccessibleOfLambdaAccessible, lambdaAccessibleOfBodyAccessible⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Proof
