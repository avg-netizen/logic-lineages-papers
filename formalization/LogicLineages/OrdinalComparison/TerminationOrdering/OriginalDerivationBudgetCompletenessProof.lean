module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetErasureProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetCompletenessProof
open Source Source.SourceMarkedSyntax RecursiveComparison OriginalDerivationBudgetSupportProof

theorem weakComplete {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : Weak Symbol arity above Gamma s t) : ∃ n,OriginalDerivationBudget.Weak Symbol arity above n Gamma s t := by
  induction h using Weak.rec
    (motive_2 := fun Gamma s t _ => ∃ n,OriginalDerivationBudget.Strict Symbol arity above n Gamma s t)
    (motive_3 := fun Gamma ss ts _ => ∃ n,OriginalDerivationBudget.WeakMatch Symbol arity above n Gamma ss ts)
    (motive_4 := fun Gamma ss ts _ => ∃ n,OriginalDerivationBudget.StrictMultiset Symbol arity above n Gamma ss ts)
    (motive_5 := fun Gamma ss ts _ => ∃ n,OriginalDerivationBudget.ReplacementMatch Symbol arity above n Gamma ss ts)
  case var v => exact ⟨1,.var 0 v⟩
  case abs s t hw ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.abs n s t hn⟩
  case fun_ f g ss ts matched he ht hp hm ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.fun_ n f g ss ts matched he ht hp hn⟩
  case put f base t hw ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.put n f base t hn⟩
  case select f base types extras requested q r t suffix hm ha hw ih =>
    obtain ⟨n,hn⟩ := ih
    exact ⟨n+1,.select n f base types extras requested q r t suffix hm ha hn⟩
  case fAbs f base types extras t hw ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.fAbs n f base types extras t hn⟩
  case copy f g base types extras target hp hw ih =>
    rename_i Gamma
    obtain ⟨n,hn⟩ := finiteBounds (fun n (p : Packed Symbol arity Gamma) => OriginalDerivationBudget.Weak Symbol arity above n Gamma
      ⟨p.1,MarkedTerm.marked f p.1 base types extras⟩ p)
      (fun n m hnm p h => raiseWeak h hnm) (argumentList target) ih
    exact ⟨n+1,.copy n f g base types extras target hp hn⟩
  case stat f g base types extras target he hm hw ihm ihw =>
    rename_i Gamma
    obtain ⟨n,hn⟩ := ihm
    obtain ⟨m,hm⟩ := finiteBounds (fun m (p : Packed Symbol arity Gamma) => OriginalDerivationBudget.Weak Symbol arity above m Gamma
      ⟨p.1,MarkedTerm.marked f p.1 base types extras⟩ p)
      (fun n m hnm p h => raiseWeak h hnm) (argumentList target) ihw
    exact ⟨max n m+1,.stat (max n m) f g base types extras target he
      (raiseMulti hn (Nat.le_max_left ..)) (fun p hp => raiseWeak (hm p hp) (Nat.le_max_right ..))⟩
  case mark s r t hm hw ih => obtain ⟨n,hn⟩ := ih; exact ⟨n+1,.mark n s r t hm hn⟩
  case nil => exact ⟨1,.nil 0⟩
  case cons s t ss ts hw hm ihw ihm =>
    obtain ⟨n,hn⟩ := ihw
    obtain ⟨m,hm⟩ := ihm
    exact ⟨max n m+1,.cons (max n m) s t ss ts (raiseWeak hn (Nat.le_max_left ..)) (raiseMatch hm (Nat.le_max_right ..))⟩
  case replace ss ts kept retained removed inserted hs ht hn hw hr ihw ihr =>
    obtain ⟨n,hn'⟩ := ihw
    obtain ⟨m,hm⟩ := ihr
    exact ⟨max n m+1,.replace (max n m) ss ts kept retained removed inserted hs ht hn
      (raiseMatch hn' (Nat.le_max_left ..)) (raiseReplacement hm (Nat.le_max_right ..))⟩
  case nil => intros; exact ⟨1,.nil 0 _⟩
  case cons =>
    intros
    rename_i Gamma removed s t rest hm hs hr ihs ihr
    obtain ⟨n,hn⟩ := ihs
    obtain ⟨m,hm'⟩ := ihr
    exact ⟨max n m+1,.cons (max n m) removed s t rest hm
      (raiseStrict hn (Nat.le_max_left ..)) (raiseReplacement hm' (Nat.le_max_right ..))⟩

theorem strictComplete {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : Strict Symbol arity above Gamma s t) : ∃ n,OriginalDerivationBudget.Strict Symbol arity above n Gamma s t := by
  cases h with
  | mark s r t hm hw =>
    obtain ⟨n,hn⟩ := weakComplete above hw
    exact ⟨n+1,.mark n s r t hm hn⟩

theorem matchComplete {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : WeakMatch Symbol arity above Gamma ss ts) : ∃ n,OriginalDerivationBudget.WeakMatch Symbol arity above n Gamma ss ts := by
  induction ss generalizing ts with
  | nil => cases h; exact ⟨1,.nil 0⟩
  | cons s ss ih => cases h with
    | cons s t ss ts hw hr =>
      obtain ⟨n,hn⟩ := weakComplete above hw
      obtain ⟨m,hm⟩ := ih hr
      exact ⟨max n m+1,.cons (max n m) s t ss ts (raiseWeak hn (Nat.le_max_left ..)) (raiseMatch hm (Nat.le_max_right ..))⟩

theorem replacementComplete {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : ReplacementMatch Symbol arity above Gamma ss ts) : ∃ n,OriginalDerivationBudget.ReplacementMatch Symbol arity above n Gamma ss ts := by
  induction ts generalizing ss with
  | nil => exact ⟨1,.nil 0 ss⟩
  | cons t ts ih => cases h with
    | cons removed s t rest hs hst hr =>
      obtain ⟨n,hn⟩ := strictComplete above hst
      obtain ⟨m,hm⟩ := ih hr
      exact ⟨max n m+1,.cons (max n m) _ _ _ _ hs (raiseStrict hn (Nat.le_max_left ..)) (raiseReplacement hm (Nat.le_max_right ..))⟩

theorem multisetComplete {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : StrictMultiset Symbol arity above Gamma ss ts) : ∃ n,OriginalDerivationBudget.StrictMultiset Symbol arity above n Gamma ss ts := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hw hr =>
    obtain ⟨n,hn'⟩ := matchComplete above hw
    obtain ⟨m,hm⟩ := replacementComplete above hr
    exact ⟨max n m+1,.replace (max n m) ss ts kept retained removed inserted hs ht hn
      (raiseMatch hn' (Nat.le_max_left ..)) (raiseReplacement hm (Nat.le_max_right ..))⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalDerivationBudgetCompletenessProof
