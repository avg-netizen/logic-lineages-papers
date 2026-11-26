import LogicLineages.PersistentMarking.NumberedWindowShiftTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowActualPairAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks

namespace LogicLineages.PersistentMarking.NumberedWindowShiftTableProof
open NumberedWindowShiftAlgorithm
open NumberedWindowArithmeticFields NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticFieldAlgorithmChecks (exact_ExactTaggedNodeCodec)
open NumberedWindowArithmeticPair (pair)

theorem lookupOfRecurrence (tab : Nat → Table) (row : Nat → Nat → Table → Row) (bound : Nat)
    (zero : tab 0 = []) (succ : ∀ n, tab (n+1) =
      tab n ++ [(List.range (bound+1)).map (fun offset => row n offset (tab n))])
    {n code offset : Nat} (codeLt : code < n) (offsetLe : offset ≤ bound) :
    earlier (tab n) code offset = row code offset (tab code) := by
  have lengths : ∀ k, (tab k).length = k := by
    intro k
    induction k with
    | zero => simp [zero]
    | succ k ih => simp [succ k,ih]
  have entry : ∀ k, code < k → (tab k)[code]? =
      some ((List.range (bound+1)).map (fun offset => row code offset (tab code))) := by
    intro k
    induction k with
    | zero => omega
    | succ k ih =>
      intro hk
      by_cases hm : code < k
      · have left : code < (tab k).length := by simpa only [lengths k] using hm
        rw [succ k,List.getElem?_append_left left]
        exact ih hm
      · have he : code = k := by omega
        subst k
        rw [succ code]
        simpa only [lengths] using
          (List.getElem?_concat_length (l := tab code)
            (a := (List.range (bound+1)).map (fun offset => row code offset (tab code))))
  unfold earlier
  rw [List.getD_eq_getElem?_getD (l := tab n),entry n codeLt]
  simp only [Option.getD_some,List.getD_eq_getElem?_getD,List.getElem?_map,
    List.getElem?_range (Nat.lt_succ_of_le offsetLe),Option.map_some]

theorem earlierExact (amount cutoff bound : Nat) {n code offset : Nat}
    (hCode : code < n) (hOffset : offset ≤ bound) :
    earlier (table amount cutoff bound n) code offset = computed amount cutoff bound code offset := by
  exact lookupOfRecurrence (table amount cutoff bound) (fun code offset t => next amount cutoff offset code t)
    bound rfl (fun _ => rfl) hCode hOffset

theorem computedNode (amount cutoff bound offset tag : Nat) (fs : List Nat) :
    (computed amount cutoff bound (encodeNode tag fs) offset).1 =
      termParts (table amount cutoff bound (encodeNode tag fs)) amount cutoff offset tag fs := by
  change termNext amount cutoff offset _ _ = _
  simp [termNext,← exact_ExactTaggedNodeCodec.2,nodeRound]

theorem computedCons (amount cutoff bound offset q r : Nat) (h : offset ≤ bound) :
    (computed amount cutoff bound (pair q r + 1) offset).2 =
      pair (computed amount cutoff bound q offset).1 (computed amount cutoff bound r offset).2 + 1 := by
  change argsNext offset (pair q r + 1) _ = _
  simp [argsNext,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound,earlierExact,← NumberedWindowActualPairAlgorithmChecks.currentPair,
    Nat.lt_succ_of_le (pairBounds q r).1,Nat.lt_succ_of_le (pairBounds q r).2,h]

theorem encodePack : encodeNode = NumberedWindowFieldAlgorithm.packNode :=
  exact_ExactTaggedNodeCodec.1

theorem encodePair : pair = NumberedWindowPairAlgorithm.pair :=
  NumberedWindowActualPairAlgorithmChecks.currentPair

end LogicLineages.PersistentMarking.NumberedWindowShiftTableProof
