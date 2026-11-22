module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDirectedRoundsNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionNumericProof
open LogicLineages.OrdinalComparison.TerminationOrdering
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open ID1Completion.InternalUnpair (left right)
open ID1Completion.InternalUnpairEvaluationProof (exactUnpairEvaluation)
open ID1Completion.InternalAcceptanceCalibrationProof (evalBranch)
open NumberedMultisetNumeric (numbersNumber)
open NumberedWindowCoverBoundsAlgorithm (Measure bounds cover)
open NumberedWindowCoverAlgorithm (grammar)
open NumberedWindowSyntaxAlgorithm (syntaxBits)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalCoverAuxApplicationsTargets (reorder)
open NumberedWindowInternalCoverSelectedGrammarTargets (selectedTerms)
open NumberedWindowInternalCoverSelectedGrammarNumericProof (exact_SelectedCoverGrammarOutputValues)
open NumberedWindowInternalSparseDirectedRoundsNumericTapeProof (vectorFour)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (vectorOne compositeThree)
open NumberedWindowInternalFactoredCoverTargets
open NumberedWindowInternalCoverSelectedGrammarOptionTargets

private theorem sameListCode (xs : List Nat) : Encodable.encode xs = numbersNumber xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rw [Encodable.encode_list_cons,Encodable.encode_nat,ih,numbersNumber,Nat.add_comm 1] <;> rfl

private theorem measuredList (H K : List Nat) (m : Measure) :
    evaluate termListAtMeasure (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ
      Encodable.encode m ::ᵥ nil) = numbersNumber (grammar H K m.2 m.1).1 := by
  let xs := Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ Encodable.encode m ::ᵥ nil
  have code : Encodable.encode m = Nat.pair m.1 m.2 := by
    cases m <;> rfl
  have read := exactUnpairEvaluation (Encodable.encode m)
  rw [code,Nat.unpair_pair] at read
  have dl : evaluate (reorder left (![2] : Fin 1 → Fin 3)) xs = m.1 := by
    change evaluate left (ofFn fun i : Fin 1 => xs.get ((![2] : Fin 1 → Fin 3) i)) = _
    rw [vectorOne]
    change evaluate left (Encodable.encode m ::ᵥ nil) = m.1
    rw [code]
    exact read.1
  have dr : evaluate (reorder right (![2] : Fin 1 → Fin 3)) xs = m.2 := by
    change evaluate right (ofFn fun i : Fin 1 => xs.get ((![2] : Fin 1 → Fin 3) i)) = _
    rw [vectorOne]
    change evaluate right (Encodable.encode m ::ᵥ nil) = m.2
    rw [code]
    exact read.2
  change evaluate selectedTerms (ofFn fun i : Fin 4 =>
    evaluate ((![(reorder left (![2] : Fin 1 → Fin 3)),.projection 0,.projection 1,
      (reorder right (![2] : Fin 1 → Fin 3))] : Fin 4 → Program 3) i) xs) = _
  rw [vectorFour]
  change evaluate selectedTerms (evaluate (reorder left (![2] : Fin 1 → Fin 3)) xs ::ᵥ
    Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ
    evaluate (reorder right (![2] : Fin 1 → Fin 3)) xs ::ᵥ nil) = _
  rw [dl,dr,sameListCode,sameListCode]
  exact (exact_SelectedCoverGrammarOutputValues H K m.1 m.2).1

theorem exact_SelectedGrammarOption : GrammarOptionCalibrated selectedGrammarOption := by
  intro H K m
  let xs := Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ Encodable.encode m ::ᵥ nil
  change evaluate Program.succ (ofFn fun _ : Fin 1 => evaluate termListAtMeasure xs) = _
  rw [vectorOne]
  change (evaluate termListAtMeasure xs).succ = _
  rw [measuredList]
  change (numbersNumber (grammar H K m.2 m.1).1).succ =
    (Encodable.encode (grammar H K m.2 m.1).1).succ
  rw [sameListCode]

private theorem rawValue (p : Program 1) (xs : List.Vector Nat 3) :
    evaluate (rawCall p) xs = run p (xs.get 2) := by
  change evaluate p (List.Vector.ofFn fun _ : Fin 1 => xs.get 2) = _
  rw [vectorOne] <;> rfl

private theorem actualGeneratorValue (M : Program 1) (H K : List Nat) (n : Nat)
    (measure : TermMeasureCalibrated M) :
    let tape := Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ nil
    evaluate (generatorCall M selectedGrammarOption) tape =
      Encodable.encode (some (grammar H K (bounds n).1.2 (bounds n).1.1).1) := by
  dsimp only
  rw [generatorCall,compositeThree,rawValue]
  change evaluate selectedGrammarOption
    (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ evaluate M (n ::ᵥ nil) ::ᵥ nil) = _
  rw [measure n]
  exact exact_SelectedGrammarOption H K (bounds n).1

theorem exact_SelectedGrammarFactoredCover
    (V M : Program 1)
    (syntaxCal : NumberedWindowInternalAuxExchangeMemoStepTargets.TermSyntaxCalibrated V)
    (measure : TermMeasureCalibrated M) :
    NumberedWindowInternalSparseCoverScratchTargets.ActualSelectedCoverOutput
      (factoredCover V M selectedGrammarOption) := by
  intro H K n
  rw [factoredCover,evalBranch,rawValue]
  change (if run V n = 0 then 0 else
    evaluate (generatorCall M selectedGrammarOption)
      (Encodable.encode H ::ᵥ Encodable.encode K ::ᵥ n ::ᵥ nil)) =
      Encodable.encode (cover H K n)
  rw [syntaxCal n,actualGeneratorValue M H K n measure]
  cases valid : (syntaxBits n).1 <;> simp [cover,valid]

#print axioms exact_SelectedGrammarOption
#print axioms exact_SelectedGrammarFactoredCover

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarOptionNumericProof
