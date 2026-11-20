import LogicLineages.PersistentMarking.NumberedWindowShiftProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowShiftChecks
open NumberedWindowShiftAlgorithm NumberedWindowShiftTargets NumberedWindowShiftProof
open NumberedWindowArithmeticSyntaxAlgorithmChecks NumberedWindowArithmeticSyntaxAlgorithmTargets
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks

theorem exact_ShiftMatrix : ExactShiftMatrix := matrix

theorem exact_ShiftOutput : ExactShiftOutput := by
  intro a c n
  unfold output
  rw [exact_ExactTermArgsGuards n]
  simp only [OriginalRow]
  apply Prod.ext
  · cases h : decodeTerm n with
    | none => rfl
    | some Q =>
      have he := (exact_TermCodec.1 n Q).mp h
      have hs := term a c (encodeTerm Q) Q 0 (by simp)
      simpa [he] using congrArg some hs
  · cases h : decodeArgs n with
    | none => rfl
    | some qs =>
      have he := (exact_ArgsCodec.1 n qs).mp h
      have hs := args a c (encodeArgs qs) qs 0 (by simp)
      simpa [he] using congrArg some hs

#print axioms exact_ShiftMatrix
#print axioms exact_ShiftOutput

end LogicLineages.PersistentMarking.NumberedWindowShiftChecks
