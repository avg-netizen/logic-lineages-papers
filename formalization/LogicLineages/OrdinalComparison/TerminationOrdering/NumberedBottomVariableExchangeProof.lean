module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeCasesProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeProof
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedPrimarySubstitution NumberedBottomVariable NumberedPrimaryExchange
open NumberedBottomVariableProof NumberedBottomVariableExchangeSupportProof
open NumberedBottomVariableExchangeCasesProof

theorem exchangeInverse {Symbol : Type} {arity : Symbol → Nat} (symbols : List Symbol) (S : List Ty)
    {Gamma : List Ty} {tau : Ty} (q : AuxTerm Symbol arity Gamma tau) :
    ∀ (Delta : List Ty) (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta),
      BottomOrVariable theta → ∀ r : Packed Symbol arity Delta,
      Exchange Symbol arity symbols S Delta (substitutePacked theta ⟨tau,q⟩) r →
      ∃ q' : Packed Symbol arity Gamma,
        Exchange Symbol arity symbols S Gamma ⟨tau,q⟩ q' ∧ substitutePacked theta q' = r := by
  induction q using AuxTerm.rec
    (motive_2 := fun Gamma types base => ∀ (Delta : List Ty)
      (theta : NumberedRewriteSyntax.Substitution Symbol arity Gamma Delta), BottomOrVariable theta →
      ∀ target : AuxArguments Symbol arity Delta types,
      ArgumentExchange Symbol arity symbols S Delta types (substituteArguments base theta) target →
      ∃ source : AuxArguments Symbol arity Gamma types,
        ArgumentExchange Symbol arity symbols S Gamma types base source ∧
        substituteArguments source theta = target)
  case var v =>
    intro Delta theta ht r hs
    rcases ht v with hb | ⟨w,hw⟩
    · simp only [substitutePacked,substitute,hb] at hs
      cases hs
    · simp only [substitutePacked,substitute,hw] at hs
      cases hs
  case lam body ih =>
    intro Delta theta ht r hs
    obtain ⟨target,hs,hr⟩ := lambdaCases hs
    obtain ⟨target',hsource,he⟩ := typedWitness (liftSubstitution theta) _ _ target
      (ih _ (liftSubstitution theta) (actualLiftBottomOrVariable Symbol arity _ _ _ theta ht) _ hs)
    exact ⟨⟨_,.lam target'⟩,.lam body target' hsource,by simp only [substitutePacked,substitute,he,hr]⟩
  case app f a ihf iha =>
    intro Delta theta ht r hs
    cases hs with
    | appFunction _ target _ hs =>
      obtain ⟨target',hsource,he⟩ := typedWitness theta _ _ target (ihf Delta theta ht _ hs)
      exact ⟨⟨_,.app target' a⟩,.appFunction f target' a hsource,
        by simp only [substitutePacked,substitute,he]⟩
    | appArgument _ _ target hs =>
      obtain ⟨target',hsource,he⟩ := typedWitness theta _ _ target (iha Delta theta ht _ hs)
      exact ⟨⟨_,.app f target'⟩,.appArgument f a target' hsource,
        by simp only [substitutePacked,substitute,he]⟩
  case bottom tau =>
    intro Delta theta ht r hs
    cases hs
  case ordinary f base ih =>
    intro Delta theta ht r hs
    rcases ordinaryCases hs with ⟨g,target,hf,hg,heq,htype,hp,hr⟩ | ⟨target,hs,hr⟩
    · obtain ⟨target',hp',he⟩ := argumentPermutationInverse theta base target hp
      exact ⟨⟨_,.ordinary g target'⟩,.ordinary f g base target' hf hg heq htype hp',
        by simp only [substitutePacked,substitute,he,hr]⟩
    · obtain ⟨target',hsource,he⟩ := ih Delta theta ht target hs
      exact ⟨⟨_,.ordinary f target'⟩,.ordinaryArguments f base target' hsource,
        by simp only [substitutePacked,substitute,he,hr]⟩
  case numbered k f tau base types extras ihb ihe =>
    intro Delta theta ht r hs
    cases hs with
    | numbered _ _ g _ _ target _ _ hf hg heq hp =>
      obtain ⟨target',hp',he⟩ := argumentPermutationInverse theta base target hp
      exact ⟨⟨tau,.numbered k g tau target' types extras⟩,
        .numbered k f g tau base target' types extras hf hg heq hp',
        by simp only [substitutePacked,substitute,he]⟩
    | numberedBase _ _ _ _ target _ _ hs =>
      obtain ⟨target',hsource,he⟩ := ihb Delta theta ht target hs
      exact ⟨⟨tau,.numbered k f tau target' types extras⟩,
        .numberedBase k f tau base target' types extras hsource,
        by simp only [substitutePacked,substitute,he]⟩
    | numberedExtras _ _ _ _ _ _ target hs =>
      obtain ⟨target',hsource,he⟩ := ihe Delta theta ht target hs
      exact ⟨⟨tau,.numbered k f tau base types target'⟩,
        .numberedExtras k f tau base types extras target' hsource,
        by simp only [substitutePacked,substitute,he]⟩
  case nil Gamma Delta theta ht target hs =>
    cases hs
  case cons Gamma sigma types q rest ihq ihr Delta theta ht target hs =>
    cases hs with
    | head _ r _ hs =>
      obtain ⟨r',hr',he⟩ := typedWitness theta _ _ r (ihq Delta theta ht _ hs)
      exact ⟨.cons r' rest,.head q r' rest hr',by simp only [substituteArguments,he]⟩
    | tail _ _ target hs =>
      obtain ⟨target',htarget,he⟩ := ihr Delta theta ht target hs
      exact ⟨.cons q target',.tail q rest target' htarget,by simp only [substituteArguments,he]⟩

theorem actualExchangeInverse : NumberedBottomVariableLiftingTargets.ActualExchangeInverse := by
  intro Symbol arity symbols S Gamma Delta theta ht q r hs
  rcases q with ⟨tau,q⟩
  exact exchangeInverse symbols S q Delta theta ht r hs

theorem actualArgumentExchangeInverse : NumberedBottomVariableLiftingTargets.ActualArgumentExchangeInverse := by
  intro Symbol arity symbols S Gamma Delta theta ht types base target hs
  induction types with
  | nil => cases hs
  | cons sigma types ih =>
    cases base with
    | cons q rest =>
      cases hs with
      | head _ r _ hs =>
        obtain ⟨r',hr',he⟩ := typedWitness theta _ _ r (exchangeInverse symbols S q Delta theta ht _ hs)
        exact ⟨.cons r' rest,.head q r' rest hr',by simp only [substituteArguments,he]⟩
      | tail _ _ target hs =>
        obtain ⟨target',htarget,he⟩ := ih rest target hs
        exact ⟨.cons q target',.tail q rest target' htarget,by simp only [substituteArguments,he]⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedBottomVariableExchangeProof
