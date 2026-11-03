module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMarkedCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedMacroCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSelectionCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedAbstractionCasesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceSharpening SourceUnmarked SourceExtendedElimination
open SourceExtendedOrdinaryCasesProof SourceExtendedMarkedCasesProof SourceExtendedMacroCasesProof
open SourceExtendedSelectionCasesProof SourceExtendedAbstractionCasesProof SourceExtendedListProof

theorem weakElimination {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : SourceExtendedComparison.Weak Symbol arity above Gamma s t) : WeakMeaning above s t := by
  induction h using SourceExtendedComparison.Weak.rec
    (motive_2 := fun Gamma s t _ => StrictMeaning above s t)
    (motive_3 := fun Gamma ss ts _ => MatchMeaning above ss ts)
    (motive_4 := fun Gamma ss ts _ => MultiMeaning above ss ts)
    (motive_5 := fun Gamma ss ts _ => ReplacementMeaning above ss ts)
  case var v => exact variableCase above v
  case abs s t hw ih => exact abstractionCase above s t ih
  case fun_ f g ss ts matched he ht hp hm ih => exact funCase above f g ss ts matched he ht hp ih
  case put f ss t hw ih => exact putCase above f ss t ih
  case select f ss types extras requested q r t suffix hm he hw ih =>
    exact selectionCase above f ss extras q r t suffix hm he ih
  case fAbs f ss types extras t hw ih => exact functionalAbstractionCase above f ss extras t ih
  case copy f g ss types extras ts hp hw ih => exact copyCase above f g ss extras ts hp ih
  case stat f g ss types extras ts he hm hw ihm ihw => exact statCase above f g ss extras ts he ihm ihw
  case in_ => apply noMarkedTarget above
  case marked1 => apply noMarkedTarget above
  case marked2 => apply noMarkedTarget above
  case dropMore f base types moreTypes extras more t hw ih => exact dropCase above f base extras more t ih
  case reorder f base typesS typesT extrasS extrasT t hp hw ih => exact reorderCase above f base extrasS extrasT t hp ih
  case addPrefixCopies f base types copyTypes extras copies t hp hw ih => exact prefixCopiesCase above f base extras copies t hp ih
  case prefixSelect f base extraTypes types extras copies q r t suffix hm hc ha hw ih =>
    exact prefixSelectionCase above f base extras copies q r t suffix hm hc ha ih
  case mark s r t hm hw ih => exact strictCase above s r t hm ih
  case nil => exact matchNil above
  case cons s t ss ts hw hm ihw ihm => exact matchCons above s t ss ts ihw ihm
  case replace ss ts kept retained removed inserted hs ht hn hw hr ihw ihr =>
    exact multiset above ss ts kept retained removed inserted hs ht hn ihw ihr
  case nil => intro removed; exact replacementNil above removed
  case cons => apply replacementCons above <;> assumption

theorem strictElimination {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : SourceExtendedComparison.Strict Symbol arity above Gamma s t) : StrictMeaning above s t := by
  cases h with
  | mark s r t hm hw => exact strictCase above s r t hm (weakElimination above hw)

theorem matchingElimination {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts) : MatchMeaning above ss ts := by
  induction ss generalizing ts with
  | nil => cases h; exact matchNil above
  | cons s ss ih =>
    cases h with
    | cons s t ss ts hw hr => exact matchCons above s t ss ts (weakElimination above hw) (ih hr)

theorem replacementElimination {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : SourceExtendedComparison.ReplacementMatch Symbol arity above Gamma ss ts) : ReplacementMeaning above ss ts := by
  induction ts generalizing ss with
  | nil => exact replacementNil above ss
  | cons t ts ih =>
    cases h with
    | cons removed s t rest hm hs hr => exact replacementCons above _ _ _ _ hm (strictElimination above hs) (ih hr)

theorem multisetElimination {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : SourceExtendedComparison.StrictMultiset Symbol arity above Gamma ss ts) : MultiMeaning above ss ts := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hw hr =>
    exact multiset above ss ts kept retained removed inserted hs ht hn
      (matchingElimination above hw) (replacementElimination above hr)

theorem actualJointElimination : SourceExtendedEliminationTargets.ActualJointElimination := by
  intro Symbol arity above
  exact ⟨fun _ _ _ h => weakElimination above h,fun _ _ _ h => strictElimination above h,
    fun _ _ _ h => matchingElimination above h,fun _ _ _ h => multisetElimination above h,
    fun _ _ _ h => replacementElimination above h⟩

theorem weakUnmarkedConservativity : SourceExtendedComparisonTargets.WeakUnmarkedConservativity := by
  intro Symbol arity above Gamma tau q s t ht hqs hst
  exact weakElimination above hst _ (.mk q s hqs) ht

theorem strictUnmarkedConservativity : SourceExtendedComparisonTargets.StrictUnmarkedConservativity := by
  intro Symbol arity above Gamma tau q s t ht hqs hst
  exact strictElimination above hst _ (.mk q s hqs) ht

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationProof
