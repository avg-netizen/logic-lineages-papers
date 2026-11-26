module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionListProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionScanProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open OriginalHereditaryAnnotatedExpansion NumberedMultisetNumeric
open OriginalHereditaryAnnotatedExpansionEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructorsEvaluationProof

def scanValues (count role typ raw jobs : Nat) := (List.range count).map (fun k =>
  decoratedValue k role typ raw
    (evaluate InternalRawListRecursion.lookup (k ::ᵥ jobs ::ᵥ nil)))

theorem stepEvaluation (k old role typ raw jobs : Nat) :
    evaluate scanStep (k ::ᵥ old ::ᵥ role ::ᵥ typ ::ᵥ raw ::ᵥ jobs ::ᵥ nil) =
      evaluate InternalApplicationValidityStackAppend.append
        (old ::ᵥ (1 + Nat.pair (decoratedValue k role typ raw
          (evaluate InternalRawListRecursion.lookup (k ::ᵥ jobs ::ᵥ nil))) 0) ::ᵥ nil) := by
  rw [scanStep,binaryCompositionEvaluation,consOfEvaluation,constantEvaluation]
  have hd : evaluate (.composition decorate
      ![.projection 0,.projection 2,.projection 3,.projection 4,
        .composition InternalRawListRecursion.lookup ![.projection 0,.projection 5]])
      (k ::ᵥ old ::ᵥ role ::ᵥ typ ::ᵥ raw ::ᵥ jobs ::ᵥ nil) =
      decoratedValue k role typ raw
        (evaluate InternalRawListRecursion.lookup (k ::ᵥ jobs ::ᵥ nil)) := by
    trans evaluate decorate (ofFn ![k,role,typ,raw,
      evaluate InternalRawListRecursion.lookup (k ::ᵥ jobs ::ᵥ nil)])
    · change evaluate decorate (ofFn fun i : Fin 5 => evaluate
        ((![.projection 0,.projection 2,.projection 3,.projection 4,
          .composition InternalRawListRecursion.lookup ![.projection 0,.projection 5]] :
            Fin 5 → Program 6) i)
          (k ::ᵥ old ::ᵥ role ::ᵥ typ ::ᵥ raw ::ᵥ jobs ::ᵥ nil)) = _
      congr 1
    · exact decorateEvaluation k role typ raw _
  rw [hd,InternalEqualityTestEvaluationProof.vectorTwo]
  rfl

theorem nativeScan (count role typ raw jobs : Nat) :
    evaluate scan (count ::ᵥ role ::ᵥ typ ::ᵥ raw ::ᵥ jobs ::ᵥ nil) =
      numbersNumber (scanValues count role typ raw jobs) := by
  induction count with
  | zero => rfl
  | succ k ih =>
    change evaluate scanStep (k ::ᵥ evaluate scan (k ::ᵥ role ::ᵥ typ ::ᵥ raw ::ᵥ jobs ::ᵥ nil)
      ::ᵥ role ::ᵥ typ ::ᵥ raw ::ᵥ jobs ::ᵥ nil) = _
    rw [stepEvaluation,ih]
    have h := OriginalContextInsertionCalibrationProof.appendNumbers
      (scanValues k role typ raw jobs)
      [decoratedValue k role typ raw (evaluate InternalRawListRecursion.lookup (k ::ᵥ jobs ::ᵥ nil))]
    simpa only [scanValues,List.range_succ,List.map_append,List.map_singleton,numbersNumber] using h

theorem decorateAllEvaluation (role typ raw : Nat) (jobs : List Nat) :
    evaluate decorateAll (ofFn ![role,typ,raw,numbersNumber jobs]) =
      numbersNumber (values role typ raw jobs) := by
  have hc : evaluate decorateAll (ofFn ![role,typ,raw,numbersNumber jobs]) =
      evaluate scan (jobs.length ::ᵥ role ::ᵥ typ ::ᵥ raw ::ᵥ numbersNumber jobs ::ᵥ nil) := by
    change evaluate scan (ofFn fun i : Fin 5 => evaluate
      ((![.composition OriginalContextInsertion.length (fun _ : Fin 1 => .projection 3),
        .projection 0,.projection 1,.projection 2,.projection 3] : Fin 5 → Program 4) i)
      (ofFn ![role,typ,raw,numbersNumber jobs])) = _
    congr 1
    apply List.Vector.ext
    intro i
    refine Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (Fin.cases ?_ (fun j => Fin.elim0 j))))) i
    · change evaluate (.composition OriginalContextInsertion.length
        (fun _ : Fin 1 => .projection (3 : Fin 4))) (ofFn ![role,typ,raw,numbersNumber jobs]) = jobs.length
      rw [unaryCompositionEvaluation]
      exact OriginalContextInsertionCalibrationProof.lengthNumbers jobs
    · rfl
    · rfl
    · rfl
    · rfl
  rw [hc,nativeScan]
  unfold scanValues values
  congr 1
  apply List.map_congr_left
  intro k hk
  rw [OriginalHereditaryAnnotatedExpansionListProof.lookupNumbers]

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryAnnotatedExpansionScanProof
