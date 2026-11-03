module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedComparisonTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEmbeddingProof
open Source Source.SourceMarkedSyntax RecursiveComparison

theorem weakEmbedding {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {s t : Packed Symbol arity Gamma} (h : Weak Symbol arity above Gamma s t) :
    SourceExtendedComparison.Weak Symbol arity above Gamma s t := by
  induction h using Weak.rec
    (motive_2 := fun Gamma s t _ => SourceExtendedComparison.Strict Symbol arity above Gamma s t)
    (motive_3 := fun Gamma ss ts _ => SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts)
    (motive_4 := fun Gamma ss ts _ => SourceExtendedComparison.StrictMultiset Symbol arity above Gamma ss ts)
    (motive_5 := fun Gamma ss ts _ => SourceExtendedComparison.ReplacementMatch Symbol arity above Gamma ss ts)
  case var v => exact .var v
  case abs s t hw ih => exact .abs s t ih
  case fun_ f g ss ts matched he ht hp hm ih => exact .fun_ f g ss ts matched he ht hp ih
  case put f ss t hw ih => exact .put f ss t ih
  case select f ss types extras requested q r t suffix hm he hw ih => exact .select f ss types extras requested q r t suffix hm he ih
  case fAbs f ss types extras t hw ih => exact .fAbs f ss types extras t ih
  case copy f g ss types extras ts hp hw ih => exact .copy f g ss types extras ts hp ih
  case stat f g ss types extras ts he hm hw ihm ihw => exact .stat f g ss types extras ts he ihm ihw
  case mark s r t hm hw ih => exact .mark s r t hm ih
  case nil => exact .nil
  case cons s t ss ts hw hr ihw ihr => exact .cons s t ss ts ihw ihr
  case replace ss ts kept retained removed inserted hs ht hn hw hr ihw ihr => exact .replace ss ts kept retained removed inserted hs ht hn ihw ihr
  case nil => intro removed; exact .nil removed
  case cons => apply SourceExtendedComparison.ReplacementMatch.cons <;> assumption

theorem strictEmbedding {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {s t : Packed Symbol arity Gamma} (h : Strict Symbol arity above Gamma s t) :
    SourceExtendedComparison.Strict Symbol arity above Gamma s t := by
  cases h with
  | mark s r t hm hw => exact .mark s r t hm (weakEmbedding hw)

theorem matchEmbedding {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)} (h : WeakMatch Symbol arity above Gamma ss ts) :
    SourceExtendedComparison.WeakMatch Symbol arity above Gamma ss ts := by
  induction ss generalizing ts with
  | nil => cases h; exact .nil
  | cons s ss ih =>
    cases h with
    | cons _ t _ ts hw hr => exact .cons s t ss ts (weakEmbedding hw) (ih hr)

theorem replacementEmbedding {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)} (h : ReplacementMatch Symbol arity above Gamma ss ts) :
    SourceExtendedComparison.ReplacementMatch Symbol arity above Gamma ss ts := by
  induction ts with
  | nil => exact .nil ss
  | cons t ts ih =>
    cases h with
    | cons _ s _ _ hm hs hr => exact .cons _ s t _ hm (strictEmbedding hs) (ih hr)

theorem multisetEmbedding {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)} (h : StrictMultiset Symbol arity above Gamma ss ts) :
    SourceExtendedComparison.StrictMultiset Symbol arity above Gamma ss ts := by
  cases h with
  | replace _ _ kept retained removed inserted hs ht hn hw hr =>
    exact .replace _ _ kept retained removed inserted hs ht hn (matchEmbedding hw) (replacementEmbedding hr)

theorem originalEmbedding : SourceExtendedComparisonTargets.OriginalEmbedding := by
  intro Symbol arity above
  exact ⟨fun _ _ _ h => weakEmbedding h,fun _ _ _ h => strictEmbedding h,
    fun _ _ _ h => matchEmbedding h,fun _ _ _ h => multisetEmbedding h,fun _ _ _ h => replacementEmbedding h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEmbeddingProof
