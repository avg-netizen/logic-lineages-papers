module
public import LogicLineages.PermittedControl.ActualMixedRowLeadingSumTargets
import LogicLineages.PermittedControl.SelectedLeadingSignCutoffStatementChecks
import LogicLineages.PermittedControl.ThresholdNoteCodeProof
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof

@[expose] public section
namespace LogicLineages.PermittedControl.ActualMixedRowLeadingSum
open OrdinalComparison FieldComparison PreparedProjection MixedSameRankResidue
open Targets (countCoreConstant)
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof

private theorem correctionPrimitive : Primrec correctionBoundCode := by
  have tag : Primrec (fun p : LowerOperandCode => p.1) := Primrec.fst
  have field : Primrec (fun p : LowerOperandCode => p.2.2) := Primrec.snd.comp Primrec.snd
  have endpoints := Primrec.snd.comp (Primrec.snd.comp field)
  have mu := Primrec.snd.comp endpoints
  have norm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp mu
  have ceiling := ofNat_primitive.comp
    (Primrec.nat_div.comp (Primrec.succ.comp norm) (Primrec.const 2))
  have correction : Primrec fun p : LowerOperandCode =>
      (1 : Int) - (((rawNormCode p.2.2.2.2.2 + 1) / 2 : Nat) : Int) := by
    simpa only [sub_eq_add_neg] using
      add_primitive.comp (Primrec.const (1 : Int)) (negate_primitive.comp ceiling)
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
    (abs_primitive.comp correction) (Primrec.const 0)

private theorem slopePrimitive : Primrec slopeBoundCode := by
  let Step := List WeightedCode × (WeightedCode × Nat)
  have weight : Primrec (fun p : Step => p.2.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have twice := Primrec.nat_mul.comp (Primrec.const 2) (abs_primitive.comp weight)
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) (Primrec.nat_add.comp twice acc).to₂

private theorem offsetPrimitive : Primrec offsetBoundCode := by
  let Step := List WeightedCode × (WeightedCode × Nat)
  have term : Primrec (fun p : Step => p.2.1) := Primrec.fst.comp Primrec.snd
  have acc : Primrec (fun p : Step => p.2.2) := Primrec.snd.comp Primrec.snd
  have absolute := abs_primitive.comp (Primrec.fst.comp term)
  have correction := correctionPrimitive.comp (Primrec.snd.comp term)
  have weighted := Primrec.nat_mul.comp absolute correction
  exact Primrec.list_foldr Primrec.id (Primrec.const 0) (Primrec.nat_add.comp weighted acc).to₂

private theorem correctionLiteral (op : LowerOperand) :
    correctionBoundCode op.code = correctionBound op := by
  cases op with
  | coordinate rank => rfl
  | ordinary rank F => rfl
  | count rank lam mu =>
      simp [correctionBoundCode,correctionBound,LowerOperand.code,longFieldCode,
        normal_norm_code,countCoreConstant]

private theorem slopeLiteral (terms : List WeightedOperand) :
    slopeBoundCode (terms.map encodeWeighted) = slopeBound terms := by
  induction terms with
  | nil => rfl
  | cons t terms next =>
      change 2 * t.1.natAbs + slopeBoundCode (terms.map encodeWeighted) =
        2 * t.1.natAbs + slopeBound terms
      rw [next]

private theorem offsetLiteral (terms : List WeightedOperand) :
    offsetBoundCode (terms.map encodeWeighted) = offsetBound terms := by
  induction terms with
  | nil => rfl
  | cons t terms next =>
      change t.1.natAbs * correctionBoundCode t.2.code +
          offsetBoundCode (terms.map encodeWeighted) =
        t.1.natAbs * correctionBound t.2 + offsetBound terms
      rw [correctionLiteral,next]

theorem exactEffectiveCutoff : ExactEffectiveCutoff := by
  constructor
  · have slope : Primrec (fun p : Int × List WeightedCode => slopeBoundCode p.2) :=
      slopePrimitive.comp Primrec.snd
    have offset : Primrec (fun p : Int × List WeightedCode => p.1.natAbs + offsetBoundCode p.2) :=
      Primrec.nat_add.comp (abs_primitive.comp Primrec.fst) (offsetPrimitive.comp Primrec.snd)
    exact (StatementChecks.fixed_selectedLeadingSignCutoffEffective.comp slope offset).to₂
  · intro c terms
    unfold rowCutoffCode
    rw [slopeLiteral,offsetLiteral]

end LogicLineages.PermittedControl.ActualMixedRowLeadingSum
