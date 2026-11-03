module
public import LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionStrictProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionProof
open Source Source.SourceMarkedSyntax RecursiveComparison RankedTree RankedPathOrder RankedReflection
open RankedReflectionSupportProof RankedReflectionOrdinaryProof RankedReflectionMarkedProof RankedReflectionStrictProof

theorem weakReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : RecursiveComparison.Weak Symbol arity above Gamma s t) :
    OrdinaryComparison above s t ∧ MarkedComparison above s t := by
  induction h using RecursiveComparison.Weak.rec
    (motive_2 := fun Gamma s t _ => StrictComparison above s t)
    (motive_3 := fun Gamma ss ts _ => WeakMatching above ss ts)
    (motive_4 := fun Gamma ss ts _ => StrictMatching above ss ts)
    (motive_5 := fun Gamma ss ts _ => Replacements above ss ts)
  case var v => exact variableCase (arity := arity) above v
  case abs s t hw ih => exact abstractionCase above s t
  case fun_ f g ss ts matched he ht hp hm ih => exact funCase above f g ss ts matched he hp ih
  case put f ss t hw ih => exact putCase above f ss t ih.2
  case select f ss types extras requested q r t suffix hm he hw ih =>
    exact selectCase above f ss types extras requested q r t suffix hm he ih.1
  case fAbs f ss types extras t hw ih => exact functionalAbstractionCase above f ss types extras t
  case copy f g ss types extras ts hp hw ih =>
    exact copyCase above f g ss types extras ts hp (fun p hp => (ih p hp).2)
  case stat f g ss types extras ts he hm hw ihm ihw =>
    exact statCase above f g ss types extras ts he ihm (fun p hp => (ihw p hp).2)
  case mark s r t hm hw ih => exact markCase above s r t hm ih.2
  case nil => exact weakMatchNil above
  case cons s t ss ts hw hm ihw ihm => exact weakMatchCons above s t ss ts ihw.1 ihm
  case replace ss ts kept retained removed inserted hs ht hn hw hr ihw ihr =>
    exact strictMatching above ss ts kept retained removed inserted hs ht hn ihw ihr
  case nil => intro removed; exact replacementNil above removed
  case cons => apply replacementCons above <;> assumption

theorem strictReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : Strict Symbol arity above Gamma s t) : StrictComparison above s t := by
  cases h with
  | mark s r t hm hw => exact markCase above s r t hm (weakReflection above hw).2

theorem matchingReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : WeakMatch Symbol arity above Gamma ss ts) : WeakMatching above ss ts := by
  induction ss generalizing ts with
  | nil => cases h; exact weakMatchNil above
  | cons s ss ih =>
    cases h with
    | cons s t ss ts hw hr => exact weakMatchCons above s t ss ts (weakReflection above hw).1 (ih hr)

theorem replacementReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : ReplacementMatch Symbol arity above Gamma ss ts) : Replacements above ss ts := by
  induction ts generalizing ss with
  | nil => exact replacementNil above ss
  | cons t ts ih =>
    cases h with
    | cons removed s t rest hm hs hr => exact replacementCons above _ _ _ _ hm (strictReflection above hs) (ih hr)

theorem multisetReflection {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : StrictMultiset Symbol arity above Gamma ss ts) : StrictMatching above ss ts := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hw hr =>
    exact strictMatching above ss ts kept retained removed inserted hs ht hn
      (matchingReflection above hw) (replacementReflection above hr)

theorem actualJointReflection : RankedReflectionTargets.ActualJointReflection := by
  intro Symbol arity above
  exact ⟨fun _ _ _ h => weakReflection above h,fun _ _ _ h => strictReflection above h,
    fun _ _ _ h => matchingReflection above h,fun _ _ _ h => multisetReflection above h,
    fun _ _ _ h => replacementReflection above h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.RankedReflectionProof
