module
public import LogicLineages.PermittedControl.OriginalPrintedRawStageQueryTargets
import LogicLineages.PermittedControl.OriginalPrintedRawConditionalQueryProof
import LogicLineages.PermittedControl.OriginalPrintedRawConditionalQueryComputableProof
import LogicLineages.PermittedControl.ActualRawStageCutoffProof
import LogicLineages.PermittedControl.ActualRawStageCutoffPrimitiveProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedRawStageQuery
open ActualBitFamilyRawLayout (RawFamily)
open ActualBitFamilyRawDriver (HighProgram)
open ActualBitFamilyRawSemanticDriver (TypedHigh Certified)
open ActualRawStageCutoff (stageBound exactRawStageCutoffMajorant stageBoundPrimitive)
open OriginalPrintedRawConditionalQuery (exactOriginalRawConditionalQuery exactOriginalRawQueryFailure
  originalRawConditionalQueryEffectivity)

theorem certifyStage (f : Nat → Nat) (B : Nat) (high : HighProgram) (children : TypedHigh)
    (h : HighAtStage f B high children) : Certified f B (stageBound B) high children := by
  intro fs nonzero
  exact ⟨exactRawStageCutoffMajorant B fs,h fs nonzero⟩

theorem exactOriginalRawStageQuery : ExactOriginalRawStageQuery := by
  intro f B high children h
  exact exactOriginalRawConditionalQuery f B (stageBound B) high children
    (certifyStage f B high children h)

theorem exactOriginalRawStageFailure : ExactOriginalRawStageFailure := by
  intro f B high
  exact exactOriginalRawQueryFailure f (stageBound B) high

theorem originalRawStageQueryEffectivity : OriginalRawStageQueryEffectivity := by
  intro f B high hf hh
  have bound : Primrec (stageBound B) :=
    stageBoundPrimitive.comp (Primrec.const B : Primrec (fun _ : RawFamily => B)) Primrec.id
  exact originalRawConditionalQueryEffectivity f (stageBound B) high hf bound.to_comp hh

end LogicLineages.PermittedControl.OriginalPrintedRawStageQuery
