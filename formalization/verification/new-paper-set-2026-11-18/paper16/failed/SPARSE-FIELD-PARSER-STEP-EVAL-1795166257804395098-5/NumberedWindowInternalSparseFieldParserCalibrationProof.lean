module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserUnpackProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserStepEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldCellEvaluationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserTableEvaluationProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserCalibrationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedWindowInternalSparseFieldCell (chosenCell)
open NumberedWindowInternalSparseFieldCellEvaluationProof (allInput)
open NumberedWindowInternalSparseFieldParser
open NumberedWindowInternalSparseFieldParserTargets
open NumberedWindowInternalSparseFieldParserRawPairProof (decodedPair tailBound)
open NumberedWindowInternalSparseFieldParserTableEvaluationProof (rowZero rowSucc lookupAt)
open NumberedWindowInternalSparseFieldParserStepEvaluationProof
  (params parserRow prependValue stepMissing stepPresent)
open NumberedWindowInternalSparseFieldParserUnpackProof (scratch casesUnpack)

theorem encoded : ActualEncodedOutput := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    cases n with
    | zero =>
      rw [parserRow,rowZero,casesUnpack.1]
      rfl
    | succ i =>
      rw [parserRow,rowSucc]
      cases found : chosenCell (i+1) with
      | none =>
        rw [stepMissing found,casesUnpack.2.1 i found]
        rfl
      | some ht =>
        obtain ⟨h,t⟩ := ht
        have hit : decode i = some (h,t) := (allInput.2 i).symm.trans found
        have code : pair h t = i := decodedPair hit
        have prior : t ≤ i := by rw [← code]; exact tailBound h t
        have smaller : t < i+1 := Nat.lt_succ_of_le prior
        have unpackCons : unpack (i+1) = (unpack t).map (fun xs => h::xs) := by
          rw [← code]
          exact casesUnpack.2.2 h t
        rw [stepPresent found,lookupAt _ _ _ _ _ prior,← parserRow,ih t smaller,
          unpackCons,prependValue]

theorem decoded : ActualDecodedOutput := by
  intro n
  rw [encoded n]
  cases h : unpack n with
  | none => rfl
  | some xs => exact scratch xs

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserCalibrationProof
