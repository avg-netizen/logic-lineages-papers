module
public import LogicLineages.PermittedControl.ActualBitFamilyRawReadCeilingTargets
import LogicLineages.OrdinalComparison.RawNormCode
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualBitFamilyRawReadCeiling
open OrdinalComparison FieldComparison
open PreparedProjection (LowerOperandCode)
open MixedSameRankResidue (WeightedCode)
open HeterogeneousSignedMatrixSlice (RawRow)
open ActualBitFamilyRawLayout (RawBitRow RawFamily)

theorem operandPrimitive : Primrec operandCode := by
  have tag : Primrec (fun op : LowerOperandCode => op.1) := Primrec.fst
  have field : Primrec (fun op : LowerOperandCode => op.2.2) := Primrec.snd.comp Primrec.snd
  have kind : Primrec (fun op : LowerOperandCode => op.2.2.1) := Primrec.fst.comp field
  have endpoints : Primrec (fun op : LowerOperandCode => op.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp field)
  have upper : Primrec (fun op : LowerOperandCode => op.2.2.2.2.1) := Primrec.fst.comp endpoints
  have lower : Primrec (fun op : LowerOperandCode => op.2.2.2.2.2) := Primrec.snd.comp endpoints
  have norm : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have bypass : PrimrecPred (fun op : LowerOperandCode => op.1 = 0 ∨ op.2.2.1 = 0) :=
    (Primrec.eq.comp tag (Primrec.const 0)).or (Primrec.eq.comp kind (Primrec.const 0))
  exact Primrec.ite bypass (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.const 2) (Primrec.nat_max.comp (norm.comp upper) (norm.comp lower)))

private theorem foldMaximum {A : Type} [Primcodable A] {cost : A → Nat} (h : Primrec cost) :
    Primrec (fun xs : List A => xs.foldr (fun a n => max (cost a) n) 0) := by
  let P := List A × (A × Nat)
  have item : Primrec (fun p : P => p.2.1) := Primrec.fst.comp Primrec.snd
  have rest : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.list_foldr Primrec.id (Primrec.const 0)
    (Primrec.nat_max.comp (h.comp item) rest).to₂

theorem termsPrimitive : Primrec termsCode :=
  foldMaximum (operandPrimitive.comp (Primrec.snd : Primrec (Prod.snd : WeightedCode → LowerOperandCode)))

theorem rowPrimitive : Primrec rowCode :=
  termsPrimitive.comp (Primrec.snd.comp (Primrec.snd : Primrec (Prod.snd : RawRow → _)))

theorem clausePrimitive : Primrec clauseCode :=
  foldMaximum (rowPrimitive.comp (Primrec.fst : Primrec (Prod.fst : RawBitRow → RawRow)))

theorem familyPrimitive : Primrec familyCode := foldMaximum clausePrimitive

theorem exactRawReadCeilingEffectivity : ExactRawReadCeilingEffectivity :=
  ⟨operandPrimitive,termsPrimitive,rowPrimitive,clausePrimitive,familyPrimitive⟩

end LogicLineages.PermittedControl.ActualBitFamilyRawReadCeiling
