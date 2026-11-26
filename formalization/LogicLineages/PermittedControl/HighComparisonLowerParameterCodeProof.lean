module
public import LogicLineages.PermittedControl.HighComparisonLowerParameterTargets
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.HighComparisonLowerParameter
open OrdinalComparison FieldComparison

private theorem noteCodeReflects {a b : NONote} (same : rawNoteEncode a.1 = rawNoteEncode b.1) :
    a = b := by
  apply Subtype.ext
  exact (rawNoteDecodeEncode a.1).symm.trans
    ((congrArg rawNoteDecode same).trans (rawNoteDecodeEncode b.1))

private theorem fieldCodeInjective : Function.Injective longFieldCode := by
  intro F G same
  cases F with
  | iterate a =>
    cases G with
    | iterate b =>
      have exponent : a = b := congrArg (fun c : LongFieldCode => c.2.1) same
      subst b
      rfl
    | entry b lam mu =>
      have impossible : (0 : Nat) = 1 := congrArg Prod.fst same
      cases impossible
  | entry a lam mu =>
    cases G with
    | iterate b =>
      have impossible : (1 : Nat) = 0 := congrArg Prod.fst same
      cases impossible
    | entry b otherLam otherMu =>
      have exponent : a = b := congrArg (fun c : LongFieldCode => c.2.1) same
      have upper : lam = otherLam := noteCodeReflects (congrArg (fun c : LongFieldCode => c.2.2.1) same)
      have lower : mu = otherMu := noteCodeReflects (congrArg (fun c : LongFieldCode => c.2.2.2) same)
      subst b
      subst otherLam
      subst otherMu
      rfl

theorem originalFieldCodeExact : OriginalFieldCodeExact := by
  refine ⟨fieldCodeInjective,?_⟩
  intro sign sign' H H' same
  exact ⟨congrArg (fun c : RawComparisonFormCode => c.2.1) same,
    fieldCodeInjective (congrArg (fun c : RawComparisonFormCode => c.2.2) same)⟩

end LogicLineages.PermittedControl.HighComparisonLowerParameter
