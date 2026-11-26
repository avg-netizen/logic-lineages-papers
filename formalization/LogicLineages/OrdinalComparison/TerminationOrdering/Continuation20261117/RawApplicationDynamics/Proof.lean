module
public import LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawLambdaDynamics.Proof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRewriteApplicationPathProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.Proof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedRewriteApplication

def ApplicationStepCases {Symbol : Type} {arity : Symbol → Nat}
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} {tau : Ty}
    (source target : AuxTerm Symbol arity Gamma tau) : Prop :=
  match source, target with
  | .app (sigma := sigma) (tau := upsilon) f a, target =>
      target = .bottom upsilon ∨
        (∃ next : AuxTerm Symbol arity Gamma (.arrow sigma upsilon),
          RawStep Symbol arity above Gamma (.arrow sigma upsilon) f next ∧
          target = .app next a) ∨
        ∃ body : AuxTerm Symbol arity (sigma :: Gamma) upsilon,
          f = .lam body ∧ target = substitute body (singleSubstitution a)
  | _, _ => True

theorem applicationStepCasesOfStep {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {source target : AuxTerm Symbol arity Gamma tau}
    (h : RawStep Symbol arity above Gamma tau source target) :
    ApplicationStepCases above source target := by
  induction h using RawStep.rec (motive_2 := fun _ _ _ _ _ => True)
  case appFunction f next a h ih => exact Or.inr (Or.inl ⟨next, h, rfl⟩)
  case beta body a => exact Or.inr (Or.inr ⟨body, rfl, rfl⟩)
  case bottom source hn => cases source <;> first | exact Or.inl rfl | trivial
  all_goals trivial

theorem applicationStepCases {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {f : AuxTerm Symbol arity Gamma (.arrow sigma tau)}
    {a : AuxTerm Symbol arity Gamma sigma} {target : AuxTerm Symbol arity Gamma tau}
    (h : RawStep Symbol arity above Gamma tau (.app f a) target) :
    target = .bottom tau ∨
      (∃ next : AuxTerm Symbol arity Gamma (.arrow sigma tau),
        RawStep Symbol arity above Gamma (.arrow sigma tau) f next ∧
        target = .app next a) ∨
      ∃ body : AuxTerm Symbol arity (sigma :: Gamma) tau,
        f = .lam body ∧ target = substitute body (singleSubstitution a) :=
  applicationStepCasesOfStep h

def ApplicationPathCases {Symbol : Type} {arity : Symbol → Nat}
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} {tau : Ty}
    (source target : AuxTerm Symbol arity Gamma tau) : Prop :=
  match source, target with
  | .app (sigma := sigma) (tau := upsilon) f a, target =>
      target = .bottom upsilon ∨
        (∃ next : AuxTerm Symbol arity Gamma (.arrow sigma upsilon),
          RawSteps Symbol arity above Gamma (.arrow sigma upsilon) f next ∧
          target = .app next a) ∨
        ∃ body : AuxTerm Symbol arity (sigma :: Gamma) upsilon,
          RawSteps Symbol arity above Gamma (.arrow sigma upsilon) f (.lam body) ∧
          RawSteps Symbol arity above Gamma upsilon
            (substitute body (singleSubstitution a)) target
  | _, _ => True

theorem applicationPathCasesOfPath {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {source target : AuxTerm Symbol arity Gamma tau}
    (h : RawSteps Symbol arity above Gamma tau source target) :
    ApplicationPathCases above source target := by
  induction h with
  | refl source =>
      cases source with
      | app f a => exact Or.inr (Or.inl ⟨f, .refl f, rfl⟩)
      | _ => trivial
  | next source next target hstep hrest ih =>
      cases source with
      | app f a =>
          rcases applicationStepCases hstep with
            hbottom | ⟨g, hfg, hnext⟩ | ⟨body, hf, hnext⟩
          · subst next
            exact Or.inl (RawLambdaDynamics.Proof.bottomPathTerminal hrest)
          · subst next
            rcases ih with hbottom | ⟨last, hpath, htarget⟩ | ⟨body, hpath, hbeta⟩
            · exact Or.inl hbottom
            · exact Or.inr (Or.inl ⟨last, .next f g last hfg hpath, htarget⟩)
            · exact Or.inr (Or.inr ⟨body, .next f g (.lam body) hfg hpath, hbeta⟩)
          · subst f
            subst next
            exact Or.inr (Or.inr ⟨body, .refl (.lam body), hrest⟩)
      | _ => trivial

theorem actualRawApplicationPathFactorization :
    Targets.ActualRawApplicationPathFactorization := by
  intro Symbol arity above Gamma sigma tau f a target
  constructor
  · intro h
    exact applicationPathCasesOfPath h
  · rintro (hbottom | ⟨next, hpath, htarget⟩ | ⟨body, hpath, hbeta⟩)
    · subst target
      exact .next _ _ _ (.bottom (.app f a) (by intro he; cases he)) (.refl _)
    · subst target
      exact NumberedRewriteApplicationPathProof.appFunction hpath a
    · exact NumberedRewriteApplicationPathProof.trans
        (NumberedRewriteApplicationPathProof.appFunction hpath a)
        (.next _ _ _ (.beta body a) hbeta)

theorem accessibleAfterRawPath {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty}
    {source target : AuxTerm Symbol arity Gamma tau}
    (hpath : RawSteps Symbol arity above Gamma tau source target)
    (hacc : Acc (fun successor source =>
      RawStep Symbol arity above Gamma tau source successor) source) :
    Acc (fun successor source =>
      RawStep Symbol arity above Gamma tau source successor) target := by
  revert hacc
  induction hpath with
  | refl source => exact fun h => h
  | next source next target hstep hrest ih =>
      intro hacc
      exact ih (hacc.inv hstep)

theorem functionAccessibleOfApplicationAccessible {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {f : AuxTerm Symbol arity Gamma (.arrow sigma tau)}
    (a : AuxTerm Symbol arity Gamma sigma)
    (h : Acc (fun successor source =>
      RawStep Symbol arity above Gamma tau source successor) (.app f a)) :
    Acc (fun successor source =>
      RawStep Symbol arity above Gamma (.arrow sigma tau) source successor) f := by
  have reflect : ∀ (source : AuxTerm Symbol arity Gamma tau),
      Acc (fun successor source =>
        RawStep Symbol arity above Gamma tau source successor) source →
      ∀ (function : AuxTerm Symbol arity Gamma (.arrow sigma tau)),
        source = .app function a →
        Acc (fun successor source =>
          RawStep Symbol arity above Gamma (.arrow sigma tau) source successor) function := by
    intro source hs
    induction hs with
    | intro source hs ih =>
        intro function hsource
        subst source
        refine Acc.intro function ?_
        intro next hnext
        exact ih (AuxTerm.app next a) (.appFunction function next a hnext) next rfl
  exact reflect (.app f a) h f rfl

theorem reachableBetaAccessibleOfApplicationAccessible {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {f : AuxTerm Symbol arity Gamma (.arrow sigma tau)}
    (a : AuxTerm Symbol arity Gamma sigma)
    (h : Acc (fun successor source =>
      RawStep Symbol arity above Gamma tau source successor) (.app f a))
    (body : AuxTerm Symbol arity (sigma :: Gamma) tau)
    (hpath : RawSteps Symbol arity above Gamma (.arrow sigma tau) f (.lam body)) :
    Acc (fun successor source =>
      RawStep Symbol arity above Gamma tau source successor)
      (substitute body (singleSubstitution a)) := by
  have hlambda := accessibleAfterRawPath
    (NumberedRewriteApplicationPathProof.appFunction hpath a) h
  exact hlambda.inv (.beta body a)

theorem applicationAccessibleOfFunctionAccessible {Symbol : Type} {arity : Symbol → Nat}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {sigma tau : Ty}
    {f : AuxTerm Symbol arity Gamma (.arrow sigma tau)}
    (a : AuxTerm Symbol arity Gamma sigma)
    (h : Acc (fun successor source =>
      RawStep Symbol arity above Gamma (.arrow sigma tau) source successor) f)
    (hbeta : ∀ body : AuxTerm Symbol arity (sigma :: Gamma) tau,
      RawSteps Symbol arity above Gamma (.arrow sigma tau) f (.lam body) →
      Acc (fun successor source =>
        RawStep Symbol arity above Gamma tau source successor)
        (substitute body (singleSubstitution a))) :
    Acc (fun successor source =>
      RawStep Symbol arity above Gamma tau source successor) (.app f a) := by
  revert hbeta
  induction h with
  | intro f hf ih =>
      intro hbeta
      refine Acc.intro (AuxTerm.app f a) ?_
      intro target hstep
      rcases applicationStepCases hstep with
        hbottom | ⟨next, hnext, htarget⟩ | ⟨body, hf, htarget⟩
      · subst target
        exact RawLambdaDynamics.Proof.bottomAccessible above Gamma tau
      · subst target
        apply ih next hnext
        intro body hpath
        exact hbeta body (.next f next (.lam body) hnext hpath)
      · subst f
        subst target
        exact hbeta body (.refl (.lam body))

theorem actualRawApplicationAccessibilityEquivalence :
    Targets.ActualRawApplicationAccessibilityEquivalence := by
  intro Symbol arity above Gamma sigma tau f a
  constructor
  · intro h
    exact ⟨functionAccessibleOfApplicationAccessible a h,
      reachableBetaAccessibleOfApplicationAccessible a h⟩
  · rintro ⟨hf, hbeta⟩
    exact applicationAccessibleOfFunctionAccessible a hf hbeta

end LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.Continuation20261117.RawApplicationDynamics.Proof
