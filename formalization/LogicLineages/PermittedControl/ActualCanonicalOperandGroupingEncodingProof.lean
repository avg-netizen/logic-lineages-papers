module
public import LogicLineages.PermittedControl.ActualCanonicalOperandGroupingTargets
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
open OrdinalComparison PreparedProjection FieldComparison

private theorem noteBytes : Function.Injective (fun a : NONote => rawNoteEncode a.1) := by
  intro a b h
  apply Subtype.ext
  simpa only [rawNoteDecodeEncode] using congrArg rawNoteDecode h

private theorem fieldBytes : Function.Injective longFieldCode := by
  intro a b h
  have tag := congrArg Prod.fst h
  have iterate := congrArg (fun bytes : LongFieldCode => bytes.2.1) h
  have lam := congrArg (fun bytes : LongFieldCode => bytes.2.2.1) h
  have mu := congrArg (fun bytes : LongFieldCode => bytes.2.2.2) h
  cases a <;> cases b
  · exact congrArg ValueField.iterate iterate
  · exact False.elim (Nat.zero_ne_one tag)
  · exact False.elim (Nat.one_ne_zero tag)
  · rename_i i l m j l' m'
    have hi : i = j := iterate
    have hl : l = l' := noteBytes lam
    have hm : m = m' := noteBytes mu
    subst j
    subst l'
    subst m'
    rfl

theorem exactOperandEncoding : ExactOperandEncoding := by
  have operand : Function.Injective LowerOperand.code := by
    intro a b h
    have tag := congrArg Prod.fst h
    have rank := congrArg (fun bytes : LowerOperandCode => bytes.2.1) h
    have key := congrArg (fun bytes : LowerOperandCode => bytes.2.2) h
    cases a <;> cases b
    · exact congrArg LowerOperand.coordinate rank
    · exact False.elim (Nat.zero_ne_one tag)
    · exact False.elim ((by decide : (0 : Nat) ≠ 2) tag)
    · exact False.elim (Nat.one_ne_zero tag)
    · exact congrArg₂ LowerOperand.ordinary rank (fieldBytes key)
    · exact False.elim ((by decide : (1 : Nat) ≠ 2) tag)
    · exact False.elim ((by decide : (2 : Nat) ≠ 0) tag)
    · exact False.elim ((by decide : (2 : Nat) ≠ 1) tag)
    · rename_i i l m j l' m'
      have hr : i = j := rank
      have hk : ValueField.entry 0 l m = .entry 0 l' m' := fieldBytes key
      obtain ⟨_,hl,hm⟩ := ValueField.entry.inj hk
      subst j
      subst l'
      subst m'
      rfl
  refine ⟨operand,?_⟩
  intro a b equal
  obtain ⟨weight,key⟩ := Prod.mk.inj equal
  exact Prod.ext weight (operand key)

end LogicLineages.PermittedControl.ActualCanonicalOperandGrouping
