module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSupportTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowReduction NumberedRenamingSupport
open NumberedPrimarySupportProof NumberedOperationSupportProof

theorem stepSupport {Symbol : Type} {arity : Symbol → Nat} {symbols : List Symbol} {S : List Ty}
    {above : Symbol → Symbol → Prop} {Gamma : List Ty} {tau : Ty} {q r : AuxTerm Symbol arity Gamma tau}
    (h : WindowStep Symbol arity symbols S above Gamma tau q r) :
    ∀ P : VariablePredicate Gamma, supports P q → supports P r := by
  induction h using WindowStep.rec
    (motive_2 := fun Gamma types base target _ => ∀ P : VariablePredicate Gamma,
      supportsArguments P base → supportsArguments P target)
  case put label f base => intro P hp; exact ⟨hp,trivial⟩
  case select label f base types extras ts selected hm =>
    intro P hp
    apply (actualApplyArgumentsSupport Symbol arity _ P ts _ selected _).mpr
    constructor
    · rcases List.mem_append.mp hm with hb | he
      · exact (actualArgumentSupportList Symbol arity _ _ P base).mp hp.1 _ hb
      · exact (actualArgumentSupportList Symbol arity _ _ P extras).mp hp.2 _ he
    · exact actualSelfArgumentsSupport Symbol arity _ P label f base types extras ts hp.1 hp.2
  case copy label f g base types extras hg hw =>
    intro P hp
    exact actualSelfArgumentsSupport Symbol arity _ P label f base types extras _ hp.1 hp.2
  case mul label f g base types extras target hg hm hw =>
    intro P hp
    apply (actualArgumentSupportList Symbol arity _ _ P target).mpr
    exact NumberedMarkSupportProof.actualPrimitiveMultisetSupport Symbol arity _ P _ _ hm
      ((actualArgumentSupportList Symbol arity _ _ P base).mp hp.1)
  case abs label f base types extras =>
    intro P hp
    exact (actualOpenNumberedSupport Symbol arity _ P label f _ _ base types extras).mpr hp
  case ordinaryArguments f base target h ih => intro P hp; exact ih P hp
  case numberedBase label f tau base target types extras h ih => intro P hp; exact ⟨ih P hp.1,hp.2⟩
  case numberedExtras label f tau base types extras target h ih => intro P hp; exact ⟨hp.1,ih P hp.2⟩
  case appFunction q r a h ih => intro P hp; exact ⟨ih P hp.1,hp.2⟩
  case lam q r h ih => intro P hp; exact ih (liftPredicate P) hp
  case beta body a =>
    intro P hp
    apply NumberedSupportSubstitutionProof.actualTermSupportSubstitution Symbol arity _ _ (liftPredicate P) P
      (singleSubstitution a) _ body hp.1
    intro upsilon v hv
    cases v with
    | here => exact hp.2
    | there v => exact hv
  case bottom q hn => intros; trivial
  case head Gamma sigma types q r rest h ih P hp => exact ⟨ih P hp.1,hp.2⟩
  case tail Gamma sigma types q rest target h ih P hp => exact ⟨hp.1,ih P hp.2⟩

theorem actualStepSupport : NumberedStepSupportTargets.ActualStepSupport := by
  intro Symbol arity symbols S above Gamma P tau q r h hp
  exact stepSupport h P hp

theorem actualArgumentStepSupport : NumberedStepSupportTargets.ActualArgumentStepSupport := by
  intro Symbol arity symbols S above Gamma P types base target h hp
  induction types with
  | nil => cases h
  | cons sigma types ih => cases h with
    | head q r rest hs => exact ⟨stepSupport hs P hp.1,hp.2⟩
    | tail q rest target hs => exact ⟨hp.1,ih rest target hs hp.2⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepSupportProof
