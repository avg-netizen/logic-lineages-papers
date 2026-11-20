import LogicLineages.PersistentMarking.NumberedWindowArithmeticBinderRootTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticRootComparisonProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeAtomsChecks
import LogicLineages.PersistentMarking.NumberedWindowShiftChecks
import LogicLineages.PersistentMarking.NumberedWindowRawContextFrameView

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticFreshRootProof
open NumberedWindowArithmeticBinderRootTargets NumberedWindowBinderRootAlgorithm
open NumberedWindowRawWitnessRootBits NumberedWindowSyntax NumberedWindowArithmeticTermCode
open NumberedWindowArithmeticTyCode NumberedWindowArithmeticHeadCode NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticFieldAlgorithmChecks NumberedWindowArithmeticRootComparisonProof
open NumberedWindowArithmeticTermCodeChecks NumberedWindowRawContextFrameView

theorem parse (q : NTerm) : NumberedWindowFieldAlgorithm.unpackNode (encodeTerm q) = some (view q) := by
  cases q <;> exact readNode _ _

private theorem listAppend (xs ys : NArgs) : (xs.append ys).toList = xs.toList ++ ys.toList := by
  cases xs with
  | nil => rfl
  | cons x xs => simp only [NArgs.append,NArgs.toList,List.cons_append,listAppend xs ys]

private theorem packArgs (xs : NArgs) :
    NumberedWindowFieldAlgorithm.pack (xs.toList.map encodeTerm) = encodeArgs xs := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    change NumberedWindowPairAlgorithm.pair _ (NumberedWindowFieldAlgorithm.pack _) + 1 =
      NumberedWindowArithmeticPair.pair _ (encodeArgs xs) + 1
    rw [← NumberedWindowActualPairAlgorithmChecks.currentPair,packArgs]

private theorem shifted (xs : NArgs) : (NumberedWindowShiftAlgorithm.output 1 0 (encodeArgs xs)).2 =
    some (encodeArgs (shiftArgs 1 0 xs)) := by
  rw [NumberedWindowShiftChecks.exact_ShiftOutput]
  simp [exact_ArgsCodec.2.1]

private theorem body (f σ τ k bs es) :
    freshBody (encodeHead f) (encodeTy σ) (encodeTy τ) k (encodeArgs bs) (encodeArgs es) =
      some (encodeTerm (.lam σ (openNumbered f σ τ k bs es))) := by
  let xs := shiftArgs 1 0 es
  have appendCode := packArgs (xs.append (.cons (.bound σ 0) .nil))
  simp only [listAppend,NArgs.toList,List.map_append,List.map_cons,List.map_nil,encodeTerm,
    exact_ExactTaggedNodeCodec.1] at appendCode
  simp only [freshBody,shifted,Option.bind_eq_bind,Option.bind_some,NumberedWindowArithmeticExchangeAtomsChecks.exact_EncodedArguments
    (shiftArgs 1 0 es),Option.pure_def,openNumbered,encodeTerm,exact_ExactTaggedNodeCodec.1]
  rw [appendCode]

theorem fabsExact : ExactFAbsRoot := by
  intro S K
  funext a b
  apply onCodes
  intro q r
  simp only [parse,Option.any_some]
  cases q with
  | numbered f t k bs es =>
    cases k with
    | zero => cases t <;> rfl
    | succ k =>
      cases t with
      | ground => rfl
      | arrow σ τ =>
        simp only [view,fabsRow,List.getD_eq_getElem?_getD,List.getElem?_cons_succ,List.getElem?_cons_zero,
          Option.getD_some,encodeTy,Nat.pred_succ,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,
          pairRound,Option.any_some,body]
        exact NumberedWindowArithmeticExchangeAtomsChecks.exact_LiteralEquality.1 _ _
  | _ => rfl
end LogicLineages.PersistentMarking.NumberedWindowArithmeticFreshRootProof
