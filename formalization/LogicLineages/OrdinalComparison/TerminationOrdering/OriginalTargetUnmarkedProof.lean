module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalTargetUnmarkedTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OriginalTargetUnmarkedProof
open Source Source.SourceMarkedSyntax RecursiveComparison SourceUnmarked SourceExtendedElimination

theorem argumentsFromList {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : Arguments Symbol arity Gamma types) (H : AllUnmarked (argumentList args)) :
    ArgumentsUnmarked Symbol arity Gamma args := by
  induction types with
  | nil => cases args; exact .nil
  | cons tau types ih => cases args with
    | cons q rest => exact .cons q rest (H _ (List.mem_cons_self ..)) (ih rest (fun p hp => H p (List.mem_cons_of_mem _ hp)))

theorem allCons {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (t : Packed Symbol arity Gamma) (ts : List (Packed Symbol arity Gamma))
    (ht : Unmarked Symbol arity Gamma t.2) (hrest : AllUnmarked ts) : AllUnmarked (t::ts) := by
  intro p hp
  rcases List.mem_cons.mp hp with he | hm
  · subst p; exact ht
  · exact hrest p hm

theorem allNil {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} :
    AllUnmarked ([] : List (Packed Symbol arity Gamma)) := by intro p hp; cases hp

theorem allPermutedAppend {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (ts retained inserted : List (Packed Symbol arity Gamma)) (hp : ts.Perm (retained++inserted))
    (hr : AllUnmarked retained) (hi : AllUnmarked inserted) : AllUnmarked ts := by
  intro p hm
  rcases List.mem_append.mp (hp.subset hm) with hret | hins
  · exact hr p hret
  · exact hi p hins

theorem weakTarget {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : Weak Symbol arity above Gamma s t) : Unmarked Symbol arity Gamma t.2 := by
  induction h using Weak.rec
    (motive_2 := fun Gamma s t _ => Unmarked Symbol arity Gamma t.2)
    (motive_3 := fun Gamma ss ts _ => AllUnmarked ts)
    (motive_4 := fun Gamma ss ts _ => AllUnmarked ts)
    (motive_5 := fun Gamma ss ts _ => AllUnmarked ts)
  case var v => exact .var v
  case abs s t hw ih => exact .lam t ih
  case fun_ f g ss ts matched he ht hp hm ih => exact .ordinary g ts (argumentsFromList ts (fun p hmem => ih p (hp.subset hmem)))
  case put f base t hw ih => exact ih
  case select f base types extras requested q r t suffix hm ha hw ih => exact ih
  case fAbs f base types extras t hw ih => exact .lam t ih
  case copy f g base types extras ts hp hw ih => exact .ordinary g ts (argumentsFromList ts ih)
  case stat f g base types extras ts he hm hw ihm ihw => exact .ordinary g ts (argumentsFromList ts ihw)
  case mark s r t hm hw ih => exact ih
  case nil => exact allNil
  case cons s t ss ts hw hm ihw ihm => exact allCons t ts ihw ihm
  case replace ss ts kept retained removed inserted hs ht hn hm hr ihm ihr => exact allPermutedAppend ts retained inserted ht ihm ihr
  case nil => intros; exact allNil
  case cons => apply allCons <;> assumption

theorem strictTarget {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {s t : Packed Symbol arity Gamma}
    (h : Strict Symbol arity above Gamma s t) : Unmarked Symbol arity Gamma t.2 := by
  cases h with
  | mark s r t hm hw => exact weakTarget above hw

theorem matchTarget {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : WeakMatch Symbol arity above Gamma ss ts) : AllUnmarked ts := by
  induction ss generalizing ts with
  | nil => cases h; exact allNil
  | cons s ss ih => cases h with
    | cons s t ss ts hw hr => exact allCons t ts (weakTarget above hw) (ih hr)

theorem replacementTarget {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : ReplacementMatch Symbol arity above Gamma ss ts) : AllUnmarked ts := by
  induction ts generalizing ss with
  | nil => exact allNil
  | cons t ts ih => cases h with
    | cons removed s t rest hs hst hr => exact allCons t _ (strictTarget above hst) (ih hr)

theorem multisetTarget {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty}
    (above : Symbol → Symbol → Prop) {ss ts : List (Packed Symbol arity Gamma)}
    (h : StrictMultiset Symbol arity above Gamma ss ts) : AllUnmarked ts := by
  cases h with
  | replace ss ts kept retained removed inserted hs ht hn hm hr => exact allPermutedAppend ts retained inserted ht (matchTarget above hm) (replacementTarget above hr)

theorem actualFiveWayTargetNormality : OriginalTargetUnmarkedTargets.ActualFiveWayTargetNormality := by
  intro Symbol arity above
  exact ⟨fun _ _ _ h => weakTarget above h,fun _ _ _ h => strictTarget above h,
    fun _ _ _ h => matchTarget above h,fun _ _ _ h => multisetTarget above h,
    fun _ _ _ h => replacementTarget above h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OriginalTargetUnmarkedProof
