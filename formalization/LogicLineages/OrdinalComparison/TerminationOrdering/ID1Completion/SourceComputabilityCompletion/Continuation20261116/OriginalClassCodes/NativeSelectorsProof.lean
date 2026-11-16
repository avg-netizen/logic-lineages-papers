module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeMapProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeSelectorsProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open Continuation20261114 Continuation20261115
/-- Actual input layout, without any validity or canonical-image hypothesis. -/
def input (root raw syms ts table gam : Nat) : List.Vector Nat 2 :=
  ofFn ![Nat.pair root raw,Nat.pair (Nat.pair (Nat.pair syms ts) table) gam]

theorem rootValue (root raw syms ts table gam : Nat) :
    evaluate rootType (input root raw syms ts table gam) = root := by
  simp only [rootType,leftOfEvaluation,projectionEvaluation,input,List.Vector.get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair]
theorem rawValue (root raw syms ts table gam : Nat) :
    evaluate seedRaw (input root raw syms ts table gam) = raw := by
  simp only [seedRaw,rightOfEvaluation,projectionEvaluation,input,List.Vector.get_ofFn,Matrix.cons_val_zero,Nat.unpair_pair]
theorem symbolsValue (root raw syms ts table gam : Nat) :
    evaluate symbols (input root raw syms ts table gam) = syms := by
  simp only [symbols,window,context,leftOfEvaluation,projectionEvaluation,input,List.Vector.get_ofFn,Matrix.cons_val_one,Matrix.cons_val_zero,Nat.unpair_pair]
theorem typesValue (root raw syms ts table gam : Nat) :
    evaluate types (input root raw syms ts table gam) = ts := by
  simp only [types,window,context,leftOfEvaluation,rightOfEvaluation,projectionEvaluation,input,List.Vector.get_ofFn,Matrix.cons_val_one,Matrix.cons_val_zero,Nat.unpair_pair]
theorem gammaValue (root raw syms ts table gam : Nat) :
    evaluate gamma (input root raw syms ts table gam) = gam := by
  simp only [gamma,rightOfEvaluation,projectionEvaluation,input,List.Vector.get_ofFn,Matrix.cons_val_one,Matrix.cons_val_zero,Nat.unpair_pair]

theorem boundValue (root raw syms ts table : Nat) (Gamma : List Source.Ty) :
    evaluate bound (input root raw syms ts table (Encodable.encode Gamma)) = Gamma.length := by
  rw [bound,unaryCompositionEvaluation,gammaValue]
  exact OriginalContextInsertionCalibrationProof.lengthContext Gamma

theorem boundsValue (n : Nat) (root syms ts table gam : Nat) (code : Code (Fin n)) :
    evaluate (bounds n) (input root (codeNumber code) syms ts table gam) =
      Encodable.encode (NumberedSyntaxBoundsPrimrec.codeBounds code) := by
  rw [bounds,unaryCompositionEvaluation,rawValue,OriginalCodeBoundsRecursion.NativeProof.nativeBounds]
  simp only [List.Vector.get_ofFn,Matrix.cons_val_zero,NumberedNumericDecodingProof.codeRoundTrip,Option.map_some,Option.getD_some]

theorem sizeValue (n : Nat) (root syms ts table gam : Nat) (code : Code (Fin n)) :
    evaluate (size n) (input root (codeNumber code) syms ts table gam) =
      (NumberedSyntaxBoundsPrimrec.codeBounds code).1 := by
  rw [size,leftOfEvaluation,boundsValue]
  exact congrArg Prod.fst (Nat.unpair_pair _ _)

theorem labelValue (n : Nat) (root syms ts table gam : Nat) (code : Code (Fin n)) :
    evaluate (labels n) (input root (codeNumber code) syms ts table gam) =
      (NumberedSyntaxBoundsPrimrec.codeBounds code).2 := by
  rw [labels,rightOfEvaluation,boundsValue]
  exact congrArg Prod.snd (Nat.unpair_pair _ _)

theorem fuelValue (n : Nat) (root syms ts table gam : Nat) (code : Code (Fin n)) :
    evaluate (fuel n) (input root (codeNumber code) syms ts table gam) =
      2 * (NumberedSyntaxBoundsPrimrec.codeBounds code).1 := by
  rw [fuel,addOfEvaluation,sizeValue]
  omega
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeSelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeSelectorsProof
