module
public import LogicLineages.PermittedControl.ActualRawComparisonCeilingTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.PermittedControl.ShortFieldEffectivityProof
import LogicLineages.OrdinalComparison.RawComparisonProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawComparisonCeiling
open OrdinalComparison FieldComparison PreparedProjection
open SelectedCountOnlyClass (omegaSquareNote)
open ActualCountCoreLabels (rawTag rawLabel)

private theorem rawCountTagPrimitive :
    Primrec (fun p : Nat × Nat => rawTag p.1 p.2) := by
  let A := Nat × Nat
  have lam : Primrec (Prod.fst : A → Nat) := Primrec.fst
  have mu : Primrec (Prod.snd : A → Nat) := Primrec.snd
  have norm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have guard := closedProperEntryDomainExact.1.comp (lam.pair (mu.pair (norm.comp lam)))
  have short := shortFieldPreprocessingEffective.2.1.comp lam mu
  have eta := ordinalAddCodeEffective.comp mu (Primrec.const (rawNoteEncode omegaSquareNote.1))
  have cmp := rawComparisonPrimitiveRecursive.comp eta lam
  have shape : Primrec (fun p : A =>
      if rawComparisonCode (ordinalAddCode p.2 (rawNoteEncode omegaSquareNote.1)) p.1 = 1 then 2
      else if rawComparisonCode (ordinalAddCode p.2 (rawNoteEncode omegaSquareNote.1)) p.1 = 0 then 3 else 0) :=
    Primrec.ite (Primrec.eq.comp cmp (Primrec.const 1)) (Primrec.const 2)
      (Primrec.ite (Primrec.eq.comp cmp (Primrec.const 0)) (Primrec.const 3) (Primrec.const 0))
  have middle := Primrec.ite (Primrec.eq.comp short (Primrec.const 0)) shape (Primrec.const 1)
  apply (Primrec.cond guard middle (Primrec.const 0)).of_eq
  rintro ⟨lam,mu⟩
  cases h : closedProperEntryGuard (lam,mu,rawNormCode lam) <;> rfl

private theorem rawCountLabelPrimitive :
    Primrec (fun p : Nat × Nat => rawLabel p.1 p.2) := by
  let A := Nat × Nat
  have lam : Primrec (Prod.fst : A → Nat) := Primrec.fst
  have mu : Primrec (Prod.snd : A → Nat) := Primrec.snd
  have eta := ordinalAddCodeEffective.comp mu (Primrec.const (rawNoteEncode omegaSquareNote.1))
  have strict : Primrec (fun p : A => some (1,1,p.1,ordinalAddCode p.2 (rawNoteEncode omegaSquareNote.1))) :=
    Primrec.option_some.comp ((Primrec.const 1).pair ((Primrec.const 1).pair (lam.pair eta)))
  apply (Primrec.ite (Primrec.eq.comp rawCountTagPrimitive (Primrec.const 2))
    (Primrec.const (some ((0,1,0,0) : LongFieldCode)))
    (Primrec.ite (Primrec.eq.comp rawCountTagPrimitive (Primrec.const 3)) strict (Primrec.const none))).of_eq
  rintro ⟨lam,mu⟩
  unfold rawLabel
  generalize rawTag lam mu = tag
  cases tag with
  | zero => rfl
  | succ a =>
    cases a with
    | zero => rfl
    | succ b =>
      cases b with
      | zero => rfl
      | succ c => cases c <;> rfl

theorem labelPrimitive : Primrec labelCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have rank : Primrec (fun op : LowerOperandCode => op.2.1) := Primrec.fst.comp Primrec.snd
  have field : Primrec (fun op : LowerOperandCode => op.2.2) := Primrec.snd.comp Primrec.snd
  have kind : Primrec (fun op : LowerOperandCode => op.2.2.1) := Primrec.fst.comp field
  have exp : Primrec (fun op : LowerOperandCode => op.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp field)
  have ends : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp field)
  have ignore : PrimrecPred (fun op : LowerOperandCode => op.2.2.1 = 0 ∧ op.2.2.2.1 = 0) :=
    (Primrec.eq.comp kind (Primrec.const 0)).and (Primrec.eq.comp exp (Primrec.const 0))
  have ord : Primrec (fun op : LowerOperandCode =>
      if op.2.2.1 = 0 ∧ op.2.2.2.1 = 0 then none else some (op.2.1,op.2.2)) :=
    Primrec.ite ignore (Primrec.const none) (Primrec.option_some.comp (rank.pair field))
  have count : Primrec (fun op : LowerOperandCode =>
      (rawLabel op.2.2.2.2.1 op.2.2.2.2.2).map (Prod.mk op.2.1)) :=
    Primrec.option_map (rawCountLabelPrimitive.comp ends)
      (((rank.comp Primrec.fst).pair
        (Primrec.snd : Primrec (Prod.snd : LowerOperandCode × LongFieldCode → LongFieldCode))).to₂)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 1)) ord
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) count (Primrec.const none))

end LogicLineages.PermittedControl.ActualRawComparisonCeiling
