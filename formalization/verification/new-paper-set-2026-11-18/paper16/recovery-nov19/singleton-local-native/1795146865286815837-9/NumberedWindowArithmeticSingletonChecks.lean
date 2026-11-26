import LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks
namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonChecks
open NumberedWindowArithmeticSingletonTargets NumberedWindowArithmeticSingletonProof
open NumberedWindowSingletonAlgorithm NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticSyntaxAlgorithmChecks NumberedWindowArithmeticSyntaxAlgorithmTargets

theorem exact_ExactSingletonMatrix : ExactSingletonMatrix := matrix

theorem exact_ExactSingletonOutput : ExactSingletonOutput := by
  intro arg c n
  unfold output
  rw [exact_ExactTermArgsGuards arg,exact_ExactTermArgsGuards n]
  simp only [OriginalRow]
  generalize hArg : decodeTerm arg = parsed
  cases parsed with
  | none => rfl
  | some a =>
    have ha := (exact_TermCodec.1 arg a).mp hArg
    apply Prod.ext
    · change (if (decodeTerm n).isSome then some (computed arg c n n 0).1 else none) =
        (decodeTerm n).map (fun q => encodeTerm (NumberedWindowSyntax.substitute (.cons a .nil) c q))
      cases h : decodeTerm n with
      | none => rfl
      | some q =>
        have he := (exact_TermCodec.1 n q).mp h
        simpa [ha,he] using congrArg some (term a c (encodeTerm q) q 0 (by simp))
    · change (if (decodeArgs n).isSome then some (computed arg c n n 0).2 else none) =
        (decodeArgs n).map (fun qs => encodeArgs (NumberedWindowSyntax.substituteArgs (.cons a .nil) c qs))
      cases h : decodeArgs n with
      | none => rfl
      | some qs =>
        have he := (exact_ArgsCodec.1 n qs).mp h
        simpa [ha,he] using congrArg some (args a c (encodeArgs qs) qs 0 (by simp))
#print axioms exact_ExactSingletonMatrix
#print axioms exact_ExactSingletonOutput
end LogicLineages.PersistentMarking.NumberedWindowArithmeticSingletonChecks
