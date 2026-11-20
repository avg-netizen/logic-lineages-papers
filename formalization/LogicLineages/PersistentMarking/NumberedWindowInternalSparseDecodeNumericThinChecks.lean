module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeValuesThinProof
import LogicLineages.PersistentMarking.NumberedWindowSparseFloorArithmeticProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeNumericThinChecks
open NumberedWindowInternalSparseDecodeTargets
open NumberedWindowInternalSparseDecode
open NumberedWindowSparseFloorArithmeticProof (floorDecode floorAgrees)

theorem exact_CandidateValues : CandidateValues :=
  NumberedWindowInternalSparseDecodeValuesThinProof.candidates
theorem exact_GuardValue : GuardValue :=
  NumberedWindowInternalSparseDecodeValuesThinProof.guardValue

theorem exact_AllInputDecoder : AllInputDecoder := by
  intro n
  rw [← floorAgrees n]
  obtain ⟨left,right⟩ := exact_CandidateValues n
  simp only [chosenDecode,floorDecode,exact_GuardValue n,left,right]
  by_cases h : n - Nat.sqrt n * Nat.sqrt n ≤ Nat.sqrt n <;> simp [h]

#print axioms exact_CandidateValues
#print axioms exact_GuardValue
#print axioms exact_AllInputDecoder
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeNumericThinChecks
