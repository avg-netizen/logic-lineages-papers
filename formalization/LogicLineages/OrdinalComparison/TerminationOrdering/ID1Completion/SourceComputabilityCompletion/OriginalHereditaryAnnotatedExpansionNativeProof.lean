module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionScanProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedExpansion
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof

theorem expansionInputs (P : Program 4) (Q : Program 2) (role typ raw parameter : Nat) :
    evaluate (.composition P
      ![InternalApplicationCertificateConstructors.leftOf (.projection 0),
        InternalApplicationCertificateConstructors.leftOf
          (InternalApplicationCertificateConstructors.rightOf (.projection 0)),
        InternalApplicationCertificateConstructors.leftOf originalJob,
        .composition Q ![InternalApplicationCertificateConstructors.leftOf originalJob,
          InternalApplicationCertificateConstructors.rightOf originalJob]])
      (ofFn ![jobNumber role typ (Nat.pair raw parameter)]) =
      evaluate P (ofFn ![role,typ,raw,evaluate Q (ofFn ![raw,parameter])]) := by
  change evaluate P (ofFn fun i : Fin 4 => evaluate
      ((![InternalApplicationCertificateConstructors.leftOf (.projection 0),
        InternalApplicationCertificateConstructors.leftOf
          (InternalApplicationCertificateConstructors.rightOf (.projection 0)),
        InternalApplicationCertificateConstructors.leftOf originalJob,
        .composition Q ![InternalApplicationCertificateConstructors.leftOf originalJob,
          InternalApplicationCertificateConstructors.rightOf originalJob]] : Fin 4 → Program 1) i)
      (ofFn ![jobNumber role typ (Nat.pair raw parameter)])) = _
  congr 1
  apply List.Vector.ext
  intro i
  refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j)))) i <;>
    simp only [List.Vector.get_ofFn,Matrix.cons_val_succ,Matrix.cons_val_zero,Matrix.cons_val_one,
      Matrix.cons_val_two,Matrix.cons_val_three,originalJob,leftOfEvaluation,
      rightOfEvaluation,binaryCompositionEvaluation,
      OriginalHereditaryAnnotatedExpansionEvaluationProof.projectionEvaluation,
      jobNumber,Nat.unpair_pair]
  all_goals rfl

theorem expansionEvaluation (role typ raw parameter : Nat) :
    evaluate expansion (ofFn ![jobNumber role typ (Nat.pair raw parameter)]) =
      evaluate decorateAll (ofFn ![role,typ,raw,
        evaluate OriginalHereditaryExpansion.expansion (ofFn ![raw,parameter])]) :=
  expansionInputs decorateAll OriginalHereditaryExpansion.expansion role typ raw parameter

theorem nativeExpansion : OriginalHereditaryAnnotatedExpansionTargets.NativeExpansion := by
  intro n c role typ s
  rw [show OriginalHereditaryExpansion.jobNumber c s =
    Nat.pair (NumberedLeastCodeRepresentative.codeNumber s.code)
      (Nat.pair c (Encodable.encode s.context)) from rfl]
  rw [expansionEvaluation,OriginalHereditaryExpansionNativeProof.successorsCalibration,
    OriginalHereditaryAnnotatedExpansionScanProof.decorateAllEvaluation]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionNativeProof
