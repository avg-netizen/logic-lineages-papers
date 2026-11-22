module
public import LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficientTargets
import LogicLineages.PermittedControl.ActualRawCanonicalNodeMetadataPrimitiveProof
import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficient
open ActualCanonicalOperandGrouping (RawTerm)
open ActualRawCanonicalNodeMetadata (activeLabelPrimitive classFlagsPrimitive)
open ActualRawComparisonCeiling (LabelCode)
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof (mul_primitive)
open OrdinalComparison.LayeredComparison.CommonHeadCode.Program (coefficient_primitive)

theorem doubledPrimitive : Primrec doubledCode := by
  have w : Primrec (Prod.fst : RawTerm → Int) := Primrec.fst
  have tag : Primrec (fun t : RawTerm => t.2.1) := Primrec.fst.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp tag (Primrec.const 1))
    (mul_primitive.comp (Primrec.const 2) w)
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2)) w (Primrec.const 0))

private theorem weightCellPrimitive :
    Primrec (fun t : RawTerm =>
      (ActualRawCanonicalNodeMetadata.activeLabelCode t).map (fun _ => doubledCode t)) :=
  Primrec.option_map activeLabelPrimitive (doubledPrimitive.comp₂ Primrec₂.left)

theorem weightsPrimitive : Primrec weightsCode :=
  Primrec.listFilterMap Primrec.id (weightCellPrimitive.comp Primrec.snd).to₂

theorem coefficientPrimitive : Primrec₂ coefficientCode := by
  let A := List RawTerm × List Nat
  have weights : Primrec (fun p : A => weightsCode p.1) := weightsPrimitive.comp Primrec.fst
  have flags : Primrec (fun p : A => ActualRawCanonicalNodeMetadata.classFlagsCode p.1 p.2) :=
    classFlagsPrimitive.comp Primrec.fst Primrec.snd
  have h : Primrec (fun p : A => coefficientCode p.1 p.2) := coefficient_primitive.comp weights flags
  exact h.to₂

theorem exactRawCanonicalCoefficientEffectivity : ExactRawCanonicalCoefficientEffectivity :=
  ⟨doubledPrimitive,weightsPrimitive,coefficientPrimitive⟩

end LogicLineages.PermittedControl.ActualRawCanonicalNodeCoefficient
