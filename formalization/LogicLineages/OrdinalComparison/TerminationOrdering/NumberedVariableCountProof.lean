module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountTargets
public import Mathlib.Algebra.BigOperators.Group.List.Basic
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedWindowEquivalence
open NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedVariableCount

theorem argumentListCount {Symbol : Type} {arity : Symbol → Nat} {Gamma types : List Ty}
    (args : AuxArguments Symbol arity Gamma types) :
    (argumentList args |>.map packedVariableCount).sum = argumentVariableCount args := by
  induction types with
  | nil => cases args; rfl
  | cons tau types ih => cases args with
    | cons q rest => simp only [argumentList, List.map_cons, List.sum_cons,
        packedVariableCount, argumentVariableCount, ih rest]

theorem permutationCount {Symbol : Type} {arity : Symbol → Nat} {Gamma xs ys : List Ty}
    (a : AuxArguments Symbol arity Gamma xs) (b : AuxArguments Symbol arity Gamma ys)
    (hp : (argumentList a).Perm (argumentList b)) :
    argumentVariableCount a = argumentVariableCount b := by
  simpa only [argumentListCount] using (hp.map packedVariableCount).sum_eq

theorem actualPrimaryVariableCount : NumberedVariableCountTargets.ActualPrimaryVariableCount := by
  intro Symbol arity symbols S Gamma q r h
  induction h using WindowPrimary.rec
    (motive_2 := fun Gamma types base target _ => argumentVariableCount base = argumentVariableCount target)
  case refl q => rfl
  case symm h ih => exact ih.symm
  case trans h1 h2 ih1 ih2 => exact ih1.trans ih2
  case ordinary f g base target hf hg he ht hp => exact permutationCount base target hp
  case numbered k f g tau base target types extras hf hg he hp =>
    exact congrArg (fun v => v + argumentVariableCount extras) (permutationCount base target hp)
  case lam q r h ih => exact ih
  case appFunction q r a h ih =>
    exact congrArg (fun v => v + variableCount a) ih
  case appArgument q a b h ih =>
    exact congrArg (fun v => variableCount q + v) ih
  case ordinaryArguments f base target h ih => exact ih
  case numberedBase k f tau base target types extras h ih =>
    exact congrArg (fun v => v + argumentVariableCount extras) ih
  case numberedExtras k f tau base types extras target h ih =>
    exact congrArg (fun v => argumentVariableCount base + v) ih
  case nil => rfl
  case cons Gamma sigma types q r rest target hq ht ihq iht =>
    exact congrArg₂ Nat.add ihq iht

theorem actualArgumentPrimaryVariableCount : NumberedVariableCountTargets.ActualArgumentPrimaryVariableCount := by
  intro Symbol arity symbols S Gamma types base target h
  induction types with
  | nil => cases h; rfl
  | cons sigma types ih => cases h with
    | cons q r rest target hq ht =>
      exact congrArg₂ Nat.add (actualPrimaryVariableCount Symbol arity symbols S Gamma _ _ hq)
        (ih rest target ht)

theorem actualRepresentativeVariableCount : NumberedVariableCountTargets.ActualRepresentativeVariableCount := by
  intro n arity symbols S hc Gamma q r hq hr he
  exact actualPrimaryVariableCount (Fin n) arity symbols S Gamma q r
    ((NumberedLeastCodeRepresentativeProof.representativeEquality n arity symbols S hc Gamma q r hq hr).mp he)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedVariableCountProof
