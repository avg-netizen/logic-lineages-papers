import LogicLineages.PersistentMarking.NumberedWindowExternalArgumentSubstitutionTargets
import LogicLineages.PersistentMarking.NumberedWindowApplicationShiftProof

namespace LogicLineages.PersistentMarking.NumberedWindowExternalPrimaryShiftProof
open NumberedWindowSyntax NumberedWindowPrimary
open NumberedWindowExternalArgumentSubstitutionTargets
open NumberedWindowApplicationShiftProof (typed baseTyped extrasTyped)

private theorem listShift (amount cutoff : Nat) (xs : NArgs) :
    (shiftArgs amount cutoff xs).toList = xs.toList.map (shift amount cutoff) := by
  cases xs with
  | nil => rfl
  | cons a rest => simp only [shiftArgs, NArgs.toList, List.map_cons, listShift amount cutoff rest]
termination_by sizeOf xs

private theorem shiftPerm (amount cutoff : Nat) {xs ys : NArgs}
    (h : xs.toList.Perm ys.toList) :
    (shiftArgs amount cutoff xs).toList.Perm (shiftArgs amount cutoff ys).toList := by
  simpa only [listShift] using h.map (shift amount cutoff)

private theorem term {S K C τ q r} (h : Primary S K C τ q r) :
    ∀ D amount cutoff, Spine.ShiftCompatible amount cutoff C D →
      Primary S K D τ (shift amount cutoff q) (shift amount cutoff r) := by
  induction h using Primary.rec (motive_2 := fun C types xs ys _ =>
    ∀ D amount cutoff, Spine.ShiftCompatible amount cutoff C D →
      OrderedPrimary S K D types (shiftArgs amount cutoff xs) (shiftArgs amount cutoff ys)) with
  | refl hq =>
    intro D amount cutoff hc
    exact .refl (typed _ D _ _ amount cutoff hq hc)
  | symm _ ih => intro D amount cutoff hc; exact .symm (ih D amount cutoff hc)
  | trans _ _ hq hr => intro D amount cutoff hc; exact .trans (hq D amount cutoff hc) (hr D amount cutoff hc)
  | ordinary hf hg he hType hbs hcs hp =>
    intro D amount cutoff hc
    exact .ordinary hf hg he hType (baseTyped _ D _ _ amount cutoff hbs hc)
      (baseTyped _ D _ _ amount cutoff hcs hc) (shiftPerm amount cutoff hp)
  | numbered hf hg he hbs hcs hes hp =>
    intro D amount cutoff hc
    exact .numbered hf hg he (baseTyped _ D _ _ amount cutoff hbs hc)
      (baseTyped _ D _ _ amount cutoff hcs hc) (extrasTyped _ D _ amount cutoff hes hc)
      (shiftPerm amount cutoff hp)
  | lam _ ih =>
    intro D amount cutoff hc
    exact .lam (ih _ amount (cutoff + 1) (SpineShiftProof.compatiblePush amount cutoff _ D hc _))
  | appFunction _ ha ih =>
    intro D amount cutoff hc
    exact .appFunction (ih D amount cutoff hc) (typed _ D _ _ amount cutoff ha hc)
  | appArgument hq _ ih =>
    intro D amount cutoff hc
    exact .appArgument (typed _ D _ _ amount cutoff hq hc) (ih D amount cutoff hc)
  | ordinaryArguments _ ih => intro D amount cutoff hc; exact .ordinaryArguments (ih D amount cutoff hc)
  | numberedBase _ he ih =>
    intro D amount cutoff hc
    exact .numberedBase (ih D amount cutoff hc) (extrasTyped _ D _ amount cutoff he hc)
  | numberedExtras hb _ ih =>
    intro D amount cutoff hc
    exact .numberedExtras (baseTyped _ D _ _ amount cutoff hb hc) (ih D amount cutoff hc)
  | nil => exact fun _ _ _ _ => .nil
  | cons _ _ ha hs =>
    rename_i D amount cutoff hc
    exact .cons (ha D amount cutoff hc) (hs D amount cutoff hc)

theorem lexical : LexicalShiftPreservesPrimary := by
  intro S K C D τ q r amount cutoff hc hp
  exact term hp D amount cutoff hc

end LogicLineages.PersistentMarking.NumberedWindowExternalPrimaryShiftProof
