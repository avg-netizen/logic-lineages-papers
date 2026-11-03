module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyBindingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication
open OriginalSpineActions ProtectedPrefix ProtectedApply ProtectedApplyBindingProof

variable {Symbol : Type} {arity : Symbol → Nat}

private theorem originalEmpty {Gamma Delta : List Ty} {sigma : Ty}
    (q : MarkedTerm Symbol arity Gamma sigma) (s : MarkedSubstitution Symbol arity Gamma Delta) :
    applyOriginalWith q s .nil rfl=some (substituteTerm q s) := by
  cases q <;> rfl

private theorem emptyFrame {Gamma Delta pre : List Ty} {sigma : Ty}
    (q : MarkedTerm Symbol arity (pre++Gamma) sigma)
    (s : MarkedSubstitution Symbol arity Gamma Delta) (consumed : Arguments Symbol arity Delta pre) :
    applyWith q (mask pre Gamma) (closeFree s consumed) .nil rfl=applyFrame q s consumed .nil rfl := by
  unfold applyFrame
  rw [emptyTuple Symbol arity _ _ _ q,originalEmpty]
  exact congrArg some (substitutionComposition q _ _ (liftFree pre s) (closePrefix consumed)).symm

/-- Context equality only reindexes literal syntax; no semantic equality is
introduced. Keeping it explicit makes the ordinary source induction retain
an arbitrary finite protected-prefix decomposition. -/
private def FrameMeaning {Omega : List Ty} {sigma : Ty} (q : MarkedTerm Symbol arity Omega sigma) : Prop :=
  ∀ (pre Gamma : List Ty) (e : Omega=pre++Gamma) (Delta : List Ty)
    (s : MarkedSubstitution Symbol arity Gamma Delta) (consumed : Arguments Symbol arity Delta pre)
    (types : List Ty) (tau : Ty) (args : Arguments Symbol arity Delta types) (h : sigma=arrows types tau),
    let q' := Eq.mp (congrArg (fun Context => MarkedTerm Symbol arity Context sigma) e) q
    applyWith q' (mask pre Gamma) (closeFree s consumed) args h=applyFrame q' s consumed args h

private theorem frameForTerm {Omega : List Ty} {sigma : Ty} (q : MarkedTerm Symbol arity Omega sigma) :
    FrameMeaning q := by
  induction q using MarkedTerm.rec (motive_2 := fun _ _ _ => True) with
  | var v =>
    intro pre Gamma e Delta s consumed types tau args h
    cases e
    change applyWith (.var v) (mask pre Gamma) (closeFree s consumed) args h=
      applyFrame (.var v) s consumed args h
    cases args with
    | nil => cases h; exact emptyFrame (.var v) s consumed
    | cons a rest =>
      rcases variableSplit pre Gamma v with ⟨w,rfl⟩ | ⟨w,rfl⟩
      · simp only [applyWith,(ProtectedPrefixProof.literalMask pre Gamma).1 w,
          ↓reduceIte,applyFrame,substituteTerm,boundNameLift,applyOriginalWith]
      · simpa only [applyWith,(ProtectedPrefixProof.literalMask pre Gamma).2 w,
          Bool.false_eq_true,↓reduceIte,closeOld,applyFrame,substituteTerm,
          ProtectedPrefixProof.oldNameLift Symbol arity Gamma Delta pre s _ w] using
          (ProtectedPrefixProof.raisedSourceApplication Symbol arity Delta pre consumed _ tau _
            (s w) (.cons a rest) h).symm
  | @lam Omega sigma upsilon body ih =>
    intro pre Gamma e Delta s consumed types tau args h
    cases e
    dsimp only
    cases args with
    | nil => cases h; exact emptyFrame (.lam body) s consumed
    | cons a rest =>
      obtain ⟨h1,h2⟩ := Ty.arrow.inj h
      cases h1
      cases h2
      have H := ih (sigma::pre) Gamma rfl Delta s (.cons a consumed) _ tau rest rfl
      dsimp only at H
      rw [consumedBinderEnvironment Symbol arity Gamma Delta pre s consumed sigma a] at H
      exact H.trans (ProtectedPrefixProof.literalBinderStep Symbol arity Gamma Delta pre s consumed
        sigma tau _ body a rest).symm
  | ordinary f base ih =>
    intro pre Gamma e Delta s consumed types tau args h
    cases e
    change applyWith (.ordinary f base) (mask pre Gamma) (closeFree s consumed) args h=
      applyFrame (.ordinary f base) s consumed args h
    cases args with
    | nil => cases h; exact emptyFrame (.ordinary f base) s consumed
    | cons a rest =>
      simp only [applyWith,applyFrame,substituteTerm,applyOriginalWith]
      rw [argumentsComposition]
      rfl
  | marked f out base extraTypes extras ihb ihe =>
    intro pre Gamma e Delta s consumed types tau args h
    cases e
    change applyWith (.marked f out base extraTypes extras) (mask pre Gamma) (closeFree s consumed) args h=
      applyFrame (.marked f out base extraTypes extras) s consumed args h
    cases args with
    | nil => cases h; exact emptyFrame (.marked f _ base extraTypes extras) s consumed
    | cons a rest =>
      simp only [applyWith,applyFrame,substituteTerm,applyOriginalWith]
      rw [argumentsComposition,argumentsComposition]
      rfl
  | nil => trivial
  | cons q rest ihq ihr => trivial

theorem literalPrefixEquation : ProtectedApplyTargets.LiteralPrefixEquation := by
  intro Symbol arity Gamma Delta pre sigma tau q s consumed types args h
  exact frameForTerm q pre Gamma rfl Delta s consumed types tau args h

theorem initialOriginalEquation : ProtectedApplyTargets.InitialOriginalEquation := by
  intro Symbol arity Gamma Delta sigma tau q s types args h
  have H := literalPrefixEquation Symbol arity Gamma Delta [] sigma tau q s .nil types args h
  have he : @Eq (MarkedSubstitution Symbol arity Gamma Delta)
      (closeFree s (.nil : Arguments Symbol arity Delta [])) s := by
    funext tau v
    exact SourceMarkedBindingProof.markedSubstitutionIdentity.1 Symbol arity Delta tau (s v)
  rw [he] at H
  exact H

end LogicLineages.OrdinalComparison.TerminationOrdering.ProtectedApplyProof
