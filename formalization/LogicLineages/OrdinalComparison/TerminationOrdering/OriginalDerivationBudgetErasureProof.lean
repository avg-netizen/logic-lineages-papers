module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetSupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetErasureProof
open Source Source.SourceMarkedSyntax RecursiveComparison

theorem weakSound {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {n : Nat} {Gamma : List Ty} {s t : Packed Symbol arity Gamma}
    (h : OriginalDerivationBudget.Weak Symbol arity above n Gamma s t) : Weak Symbol arity above Gamma s t := by
  induction h using OriginalDerivationBudget.Weak.rec
    (motive_2 := fun n Gamma s t _ => Strict Symbol arity above Gamma s t)
    (motive_3 := fun n Gamma ss ts _ => WeakMatch Symbol arity above Gamma ss ts)
    (motive_4 := fun n Gamma ss ts _ => StrictMultiset Symbol arity above Gamma ss ts)
    (motive_5 := fun n Gamma ss ts _ => ReplacementMatch Symbol arity above Gamma ss ts)
  case var n v => exact .var v
  case abs n s t hw ih => exact .abs s t ih
  case fun_ n f g ss ts matched he ht hp hm ih => exact .fun_ f g ss ts matched he ht hp ih
  case put n f base t hw ih => exact .put f base t ih
  case select n f base types extras requested q r t suffix hm ha hw ih => exact .select f base types extras requested q r t suffix hm ha ih
  case fAbs n f base types extras t hw ih => exact .fAbs f base types extras t ih
  case copy n f g base types extras ts hp hw ih => exact .copy f g base types extras ts hp ih
  case stat n f g base types extras ts he hm hw ihm ihw => exact .stat f g base types extras ts he ihm ihw
  case up n s t hw ih => exact ih
  case mark n s r t hm hw ih => exact .mark s r t hm ih
  case up n s t hw ih => exact ih
  case nil n => exact .nil
  case cons n s t ss ts hw hm ihw ihm => exact .cons s t ss ts ihw ihm
  case up n ss ts hm ih => exact ih
  case replace n ss ts kept retained removed inserted hs ht hn hm hr ihm ihr => exact .replace ss ts kept retained removed inserted hs ht hn ihm ihr
  case up n ss ts hm ih => exact ih
  case nil => intros; exact .nil _
  case cons => apply ReplacementMatch.cons <;> assumption
  case up n ss ts hm ih => exact ih

theorem strictSound {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {n : Nat} {Gamma : List Ty} {s t : Packed Symbol arity Gamma}
    (h : OriginalDerivationBudget.Strict Symbol arity above n Gamma s t) : Strict Symbol arity above Gamma s t := by
  induction n with
  | zero => cases h
  | succ n ih => cases h with
    | mark n s r t hm hw => exact .mark s r t hm (weakSound hw)
    | up n s t h => exact ih h

theorem matchSound {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {n : Nat} {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)}
    (h : OriginalDerivationBudget.WeakMatch Symbol arity above n Gamma ss ts) : WeakMatch Symbol arity above Gamma ss ts := by
  induction n generalizing ss ts with
  | zero => cases h
  | succ n ih => cases h with
    | nil n => exact .nil
    | cons n s t ss ts hw hm => exact .cons s t ss ts (weakSound hw) (ih hm)
    | up n ss ts h => exact ih h

theorem replacementSound {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {n : Nat} {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)}
    (h : OriginalDerivationBudget.ReplacementMatch Symbol arity above n Gamma ss ts) : ReplacementMatch Symbol arity above Gamma ss ts := by
  induction n generalizing ss ts with
  | zero => cases h
  | succ n ih => cases h with
    | nil n removed => exact .nil _
    | cons n removed s t rest hs hst hr => exact .cons _ _ _ _ hs (strictSound hst) (ih hr)
    | up n ss ts h => exact ih h

theorem multisetSound {Symbol : Type} {arity : Symbol → Nat} {above : Symbol → Symbol → Prop}
    {n : Nat} {Gamma : List Ty} {ss ts : List (Packed Symbol arity Gamma)}
    (h : OriginalDerivationBudget.StrictMultiset Symbol arity above n Gamma ss ts) : StrictMultiset Symbol arity above Gamma ss ts := by
  induction n with
  | zero => cases h
  | succ n ih => cases h with
    | replace n ss ts kept retained removed inserted hs ht hn hm hr => exact .replace ss ts kept retained removed inserted hs ht hn (matchSound hm) (replacementSound hr)
    | up n ss ts h => exact ih h

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetErasureProof
