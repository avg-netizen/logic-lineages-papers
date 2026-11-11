module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedArgumentSubstitutionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedPrimarySubstitutionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepProof
open Source Source.SourceMarkedSyntax Source.SourceSpecialApplication NumberedRewriteSyntax NumberedRewriteReduction
open NumberedWindowReduction NumberedPrimarySubstitution NumberedBottomVariable
open NumberedBottomVariableProof NumberedBottomVariableListProof NumberedBottomVariableMultisetProof
open NumberedBottomVariableStepSupportProof NumberedPrimarySubstitutionProof NumberedArgumentSubstitutionProof
open NumberedBottomVariableStepCasesProof

theorem stepInverse {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    (above : Symbol → Symbol → Prop) {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      BottomOrVariable theta → ∀ r : AuxTerm Symbol arity Delta tau,
      WindowStep Symbol arity symbols S above Delta tau (substitute q theta) r →
      ∃ q' : AuxTerm Symbol arity Gamma tau,
        WindowStep Symbol arity symbols S above Gamma tau q q' ∧ substitute q' theta = r := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types base => ∀ (Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta), BottomOrVariable theta →
      ∀ target : AuxArguments Symbol arity Delta types,
      WindowArgumentStep Symbol arity symbols S above Delta types (substituteArguments base theta) target →
      ∃ source : AuxArguments Symbol arity Gamma types,
        WindowArgumentStep Symbol arity symbols S above Gamma types base source ∧
        substituteArguments source theta = target)
  case var v =>
    intro Delta theta ht r hs
    rcases ht v with hb | ⟨w,hw⟩
    · simp only [substitute,hb] at hs
      cases hs with
      | bottom q hn => exact False.elim (hn rfl)
    · simp only [substitute,hw] at hs
      cases hs with
      | bottom q hn => exact ⟨.bottom _,.bottom (.var v) (by intro he; cases he),rfl⟩
  case lam body ih =>
    intro Delta theta ht r hs
    rcases (NumberedLambdaRootProof.actualLambdaStepCases Symbol arity symbols S above _ _ _
      (substitute body (liftSubstitution theta)) r).mp hs with hr | ⟨body',hb,hr⟩
    · subst r
      exact ⟨.bottom _,.bottom (.lam body) (by intro he; cases he),rfl⟩
    · obtain ⟨body'',hb'',he⟩ := ih _ (liftSubstitution theta)
        (actualLiftBottomOrVariable Symbol arity _ _ _ theta ht) body' hb
      exact ⟨.lam body'',.lam body body'' hb'',by simp only [substitute,he,hr]⟩
  case app f a ihf iha =>
    intro Delta theta ht r hs
    rcases applicationStepCases (substitute f theta) (substitute a theta) r hs with
      ⟨g,hg,hr⟩ | ⟨body,hf,hr⟩ | hr
    · obtain ⟨g',hg',he⟩ := ihf Delta theta ht g hg
      exact ⟨.app g' a,.appFunction f g' a hg',by simp only [substitute,he,hr]⟩
    · obtain ⟨body',hf',he⟩ := lambdaShapeInverse theta ht f body hf
      subst f
      refine ⟨substitute body' (singleSubstitution a),.beta body' a,?_⟩
      rw [NumberedSubstitutionCompositionProof.actualBetaSubstitution,he,hr]
    · subst r
      exact ⟨.bottom _,.bottom (.app f a) (by intro he; cases he),rfl⟩
  case bottom tau =>
    intro Delta theta ht r hs
    cases hs with
    | bottom q hn => exact False.elim (hn rfl)
  case ordinary f base ih =>
    intro Delta theta ht r hs
    rcases ordinaryCases hs with ⟨label,hr⟩ | ⟨target,hs,hr⟩ | hr
    · exact ⟨.numbered label f (headResult f) base [] .nil,.put label f base,hr.symm⟩
    · obtain ⟨source,hsource,he⟩ := ih Delta theta ht target hs
      exact ⟨.ordinary f source,.ordinaryArguments f base source hsource,
        by simp only [substitute,he,hr]⟩
    · subst r
      exact ⟨.bottom _,.bottom (.ordinary f base) (by intro he; cases he),rfl⟩
  case numbered k f tau base types extras ihb ihe =>
    intro Delta theta ht r hs
    cases hs with
    | select label _ _ _ _ selectedTypes selected hm =>
      rw [argumentListSubstitute,argumentListSubstitute,← List.map_append] at hm
      obtain ⟨selected',hm',he⟩ := memberImageInverse theta (argumentList base ++ argumentList extras)
        (arrows selectedTypes tau) selected hm
      refine ⟨applyArguments selected' (selfArguments label f base types extras selectedTypes),
        .select label f base types extras selectedTypes selected' hm',?_⟩
      rw [actualApplyArgumentsSubstitution,actualSelfArgumentsSubstitution,he]
    | copy label _ g _ _ _ hg hw =>
      refine ⟨.ordinary g (selfArguments label f base types extras (headArguments arity g)),
        .copy label f g base types extras hg hw,?_⟩
      exact congrArg (AuxTerm.ordinary g) (actualSelfArgumentsSubstitution
        Symbol arity _ Delta theta label f base types extras (headArguments arity g))
    | mul label _ g _ _ _ target hg hm hw =>
      rw [argumentListSubstitute] at hm
      obtain ⟨values,hm',hvalues⟩ := actualPrimitiveMultisetInverse Symbol arity _ Delta theta ht
        (argumentList base) (argumentList target) hm
      obtain ⟨target',hlist,he⟩ := argumentListInverse theta (headArguments arity g) target values hvalues
      refine ⟨.ordinary g target',.mul label f g base types extras target' hg ?_ hw,?_⟩
      · rw [hlist]
        exact hm'
      · simp only [substitute,he]
    | abs label _ _ _ _ =>
      refine ⟨.lam (openNumbered label f _ _ base types extras),.abs label f base types extras,?_⟩
      exact congrArg AuxTerm.lam (NumberedOpeningSubstitutionProof.actualOpenNumberedSubstitution
        Symbol arity _ Delta theta label f _ _ base types extras)
    | numberedBase _ _ _ _ target _ _ hs =>
      obtain ⟨target',hsource,he⟩ := ihb Delta theta ht target hs
      exact ⟨.numbered k f tau target' types extras,
        .numberedBase k f tau base target' types extras hsource,by simp only [substitute,he]⟩
    | numberedExtras _ _ _ _ _ _ target hs =>
      obtain ⟨target',hsource,he⟩ := ihe Delta theta ht target hs
      exact ⟨.numbered k f tau base types target',
        .numberedExtras k f tau base types extras target' hsource,by simp only [substitute,he]⟩
    | bottom q hn => exact ⟨.bottom _,.bottom (.numbered k f tau base types extras) (by intro he; cases he),rfl⟩
  case nil Gamma Delta theta ht target hs =>
    cases hs
  case cons Gamma sigma types q rest ihq ihr Delta theta ht target hs =>
    cases hs with
    | head _ r _ hs =>
      obtain ⟨r',hr',he⟩ := ihq Delta theta ht r hs
      exact ⟨.cons r' rest,.head q r' rest hr',by simp only [substituteArguments,he]⟩
    | tail _ _ target hs =>
      obtain ⟨target',htarget,he⟩ := ihr Delta theta ht target hs
      exact ⟨.cons q target',.tail q rest target' htarget,by simp only [substituteArguments,he]⟩

theorem actualStepInverse : NumberedBottomVariableLiftingTargets.ActualStepInverse := by
  intro Symbol arity symbols S above Gamma Delta theta ht tau q r hs
  exact stepInverse symbols S above q Delta theta ht r hs

theorem actualArgumentStepInverse : NumberedBottomVariableLiftingTargets.ActualArgumentStepInverse := by
  intro Symbol arity symbols S above Gamma Delta theta ht types base target hs
  induction types with
  | nil => cases hs
  | cons sigma types ih =>
    cases base with
    | cons q rest =>
      cases hs with
      | head _ r _ hs =>
        obtain ⟨r',hr',he⟩ := stepInverse symbols S above q Delta theta ht r hs
        exact ⟨.cons r' rest,.head q r' rest hr',by simp only [substituteArguments,he]⟩
      | tail _ _ target hs =>
        obtain ⟨target',htarget,he⟩ := ih rest target hs
        exact ⟨.cons q target',.tail q rest target' htarget,by simp only [substituteArguments,he]⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableStepProof
