module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationProof
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding Source.SourceSpecialApplication RecursiveComparison SourceSharpening
open SourceSharpeningApplication SourceSharpeningApplicationSupportProof SuccessfulApplicationPostProof

theorem emptyTransport {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty} {tau : Ty}
    (q u : MarkedTerm Symbol arity Gamma tau) (h : Sharp Symbol arity Gamma q u)
    (theta eta : MarkedSubstitution Symbol arity Gamma Delta)
    (H : ∀ sigma (v : Variable Gamma sigma),Sharp Symbol arity Delta (theta v) (eta v)) :
    OutputSharp (applyOriginalWith q theta .nil rfl) (applyOriginalWith u eta .nil rfl) := by
  rw [emptyWith,emptyWith]
  exact SourceSharpeningSubstitutionProof.relatedSubstitution Symbol arity Gamma Delta tau q u theta eta h H

theorem fullOriginalApplication : SourceSharpeningApplicationTargets.FullOriginalApplication := by
  intro Symbol arity Gamma Delta sigma tau types q u h
  induction h using Sharp.rec
    (motive_2 := fun _ _ _ _ _ => True)
    (motive_3 := fun _ _ _ _ _ _ _ => True)
    (motive_4 := fun _ _ _ _ _ _ _ _ => True)
    generalizing Delta tau types
  case var v =>
    intro theta eta argsA argsB Henv hArgs hsuffix
    cases argsA with
    | nil => cases hArgs; cases hsuffix; exact emptyTransport (.var v) (.var v) (.var v) theta eta Henv
    | cons a rest => cases hArgs; trivial
  case lam s t hs ih =>
    intro theta eta argsA argsB Henv hArgs hsuffix
    cases argsA with
    | nil => cases hArgs; cases hsuffix; exact emptyTransport (.lam s) (.lam t) (.lam s t hs) theta eta Henv
    | cons a restA =>
      cases hArgs with
      | cons a b restA restB hab hrest =>
        obtain ⟨hdom,hcod⟩ := Ty.arrow.inj hsuffix
        cases hdom
        cases hcod
        apply ih _ _ _ (extendEnvironment theta a) (extendEnvironment eta b) restA restB
        · intro upsilon v
          cases v with
          | here => exact hab
          | there v => exact Henv _ v
        · exact hrest
  case ordinary f baseS baseT hb ihb =>
    intro theta eta argsA argsB Henv hArgs hsuffix
    cases argsA with
    | nil => cases hArgs; cases hsuffix; exact emptyTransport _ _ (.ordinary f baseS baseT hb) theta eta Henv
    | cons a restA =>
      cases hArgs with
      | cons a b restA restB hab hrest =>
        apply Sharp.marked f tau (substituteArguments baseS theta) (substituteArguments baseT eta) _ (.cons a restA) _ (.cons b restB)
        · exact argumentsSubstitute baseS baseT hb theta eta Henv
        · exact SourceSharpeningReflexivityProof.extrasFromArguments f (substituteArguments baseS theta)
            (.cons a restA) (.cons a restA) (.cons b restB) (.cons a b restA restB hab hrest) (fun p hp => hp)
  case marked f output baseS baseT typesS extrasS typesT extrasT hb he ihb ihe =>
    intro theta eta argsA argsB Henv hArgs hsuffix
    cases argsA with
    | nil => cases hArgs; cases hsuffix; exact emptyTransport _ _ (.marked f _ baseS baseT typesS extrasS typesT extrasT hb he) theta eta Henv
    | cons a restA =>
      cases hArgs with
      | cons a b restA restB hab hrest =>
        exact appendWhole f tau (substituteArguments baseS theta) (substituteArguments baseT eta)
          (substituteArguments extrasS theta) (substituteArguments extrasT eta) (.cons a restA) (.cons b restB)
          (argumentsSubstitute baseS baseT hb theta eta Henv)
          (extrasSubstitute f baseS extrasS extrasT he theta eta Henv) (.cons a b restA restB hab hrest)
  all_goals (intros; trivial)

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceSharpeningApplicationProof
