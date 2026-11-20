import LogicLineages.PersistentMarking.NumberedWindowArithmeticMarkRootTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRawRootCodeProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticRootComparisonProof
open NumberedWindowMarkRootAlgorithm NumberedWindowArithmeticMarkRootTargets
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks NumberedWindowArithmeticFields
open NumberedWindowArithmeticRawRootCode NumberedWindowRawWitnessRootBits NumberedWindowArithmeticPathCheckBits

theorem onCodes (S K w) (f : Nat → Nat → Bool)
    (h : ∀ q r, f (encodeTerm q) (encodeTerm r) = rootBit S K w q r) (a b : Nat) :
    guarded a b (f a b) = rootOn S K w a b := by
  unfold guarded rootOn between
  rw [NumberedWindowArithmeticRawRootCodeProof.rootRound,
    NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards,
    NumberedWindowArithmeticSyntaxAlgorithmChecks.exact_ExactTermArgsGuards]
  simp only [NumberedWindowArithmeticSyntaxAlgorithmTargets.OriginalRow]
  cases ha : decodeTerm a with
  | none => rfl
  | some q =>
    cases hb : decodeTerm b with
    | none => rfl
    | some r =>
      rw [← (exact_TermCodec.1 a q).mp ha,← (exact_TermCodec.1 b r).mp hb]
      exact h q r

theorem readNode (i : Nat) (fs : List Nat) :
    NumberedWindowFieldAlgorithm.unpackNode (encodeNode i fs) = some (i,fs) := by
  rw [← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2]
  exact NumberedWindowArithmeticNodeProof.nodeRound _ _
end LogicLineages.PersistentMarking.NumberedWindowArithmeticRootComparisonProof
