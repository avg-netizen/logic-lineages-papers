module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSubstitutionTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSubstitutionProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedPrimarySubstitution
open NumberedArgumentSubstitutionProof NumberedPrimarySubstitutionProof

theorem substituteStep {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty} {q r : AuxTerm Symbol arity Gamma tau}
    (h : WindowStep Symbol arity symbols S above Gamma tau q r) :
    ∀ (Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
    substitute q theta = substitute r theta ∨
    WindowStep Symbol arity symbols S above Delta tau (substitute q theta) (substitute r theta) := by
  classical
  induction h using WindowStep.rec
    (motive_2 := fun Gamma types base target _ => ∀ (Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      substituteArguments base theta = substituteArguments target theta ∨
      WindowArgumentStep Symbol arity symbols S above Delta types
        (substituteArguments base theta) (substituteArguments target theta))
  case put label f base => intro Delta theta; exact Or.inr (.put label f _)
  case select label f base types extras ts selected hm =>
    intro Delta theta
    apply Or.inr
    simp only [substitute]
    rw [actualApplyArgumentsSubstitution,actualSelfArgumentsSubstitution]
    apply WindowStep.select label f _ types _ ts (substitute selected theta)
    rw [argumentListSubstitute,argumentListSubstitute,← List.map_append]
    exact List.mem_map.mpr ⟨_,hm,rfl⟩
  case copy label f g base types extras hg hw =>
    intro Delta theta
    apply Or.inr
    simp only [substitute]
    rw [actualSelfArgumentsSubstitution]
    exact .copy label f g _ types _ hg hw
  case mul label f g base types extras target hg hm hw =>
    intro Delta theta
    apply Or.inr
    apply WindowStep.mul label f g _ types _ _ hg _ hw
    rw [argumentListSubstitute,argumentListSubstitute]
    exact NumberedMarkSubstitutionProof.actualPrimitiveMultisetSubstitution Symbol arity _ Delta theta _ _ hm
  case abs label f base types extras =>
    intro Delta theta
    apply Or.inr
    simp only [substitute]
    rw [NumberedOpeningSubstitutionProof.actualOpenNumberedSubstitution]
    exact .abs label f _ types _
  case ordinaryArguments f base target h ih =>
    intro Delta theta
    rcases ih Delta theta with he | hs
    · exact Or.inl (congrArg (AuxTerm.ordinary f) he)
    · exact Or.inr (.ordinaryArguments f _ _ hs)
  case numberedBase label f tau base target types extras h ih =>
    intro Delta theta
    rcases ih Delta theta with he | hs
    · exact Or.inl (congrArg (fun b => AuxTerm.numbered label f tau b types (substituteArguments extras theta)) he)
    · exact Or.inr (.numberedBase label f tau _ _ types _ hs)
  case numberedExtras label f tau base types extras target h ih =>
    intro Delta theta
    rcases ih Delta theta with he | hs
    · exact Or.inl (congrArg (fun e => AuxTerm.numbered label f tau (substituteArguments base theta) types e) he)
    · exact Or.inr (.numberedExtras label f tau _ types _ _ hs)
  case appFunction q r a h ih =>
    intro Delta theta
    rcases ih Delta theta with he | hs
    · exact Or.inl (congrArg (fun f => AuxTerm.app f (substitute a theta)) he)
    · exact Or.inr (.appFunction _ _ _ hs)
  case lam q r h ih =>
    intro Delta theta
    rcases ih _ (liftSubstitution theta) with he | hs
    · exact Or.inl (congrArg AuxTerm.lam he)
    · exact Or.inr (.lam _ _ hs)
  case beta body a =>
    intro Delta theta
    apply Or.inr
    rw [NumberedSubstitutionCompositionProof.actualBetaSubstitution]
    exact .beta _ _
  case bottom q hn =>
    intro Delta theta
    by_cases he : substitute q theta = .bottom _
    · exact Or.inl he
    · exact Or.inr (.bottom _ he)
  case head Gamma sigma types q r rest h ih Delta theta =>
    rcases ih Delta theta with he | hs
    · exact Or.inl (congrArg (fun a => AuxArguments.cons a (substituteArguments rest theta)) he)
    · exact Or.inr (.head _ _ _ hs)
  case tail Gamma sigma types q rest target h ih Delta theta =>
    rcases ih Delta theta with he | hs
    · exact Or.inl (congrArg (AuxArguments.cons (substitute q theta)) he)
    · exact Or.inr (.tail _ _ _ hs)

theorem actualStepSubstitution : NumberedStepSubstitutionTargets.ActualStepSubstitution := by
  intro Symbol arity symbols S above Gamma Delta theta tau q r h
  exact substituteStep h Delta theta

theorem actualArgumentStepSubstitution : NumberedStepSubstitutionTargets.ActualArgumentStepSubstitution := by
  intro Symbol arity symbols S above Gamma Delta theta types base target h
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest hs =>
      rcases substituteStep hs Delta theta with he | hstep
      · exact Or.inl (congrArg (fun a => AuxArguments.cons a (substituteArguments rest theta)) he)
      · exact Or.inr (.head _ _ _ hstep)
    | tail q rest target hs =>
      rcases ih rest target hs with he | hstep
      · exact Or.inl (congrArg (AuxArguments.cons (substitute q theta)) he)
      · exact Or.inr (.tail _ _ _ hstep)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSubstitutionProof
