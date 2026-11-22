module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeAdmissionProof
open NumberedWindowScalarAlgorithm (Settings admitted)
open NumberedWindowAdmissionAlgorithm (Window table rawBits termNext argsNext termParts)
open NumberedWindowFieldAlgorithm (unpackNode unpack)
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowInternalAuxWindowMemoTargets (intrinsicWindow intrinsicType)
open NumberedWindowInternalSparseTypedRawTargets (packedWindow)
open NumberedWindowRawExchangeVerticesCodecProof (nodeBounds decoded)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair)

private theorem tableLength (w : Window) (n : Nat) : (table w n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier (w : Window) {n i : Nat} (bound : i < n) :
    (table w n)[i]? = some (rawBits w i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases prior : i < n
    · simp only [table,List.getElem?_append_left (tableLength w n ▸ prior)]
      exact ih prior
    · have last : i = n := by omega
      subst i
      change (table w n ++ [rawBits w n])[n]? = some (rawBits w n)
      simpa only [tableLength] using (List.getElem?_concat_length (l := table w n) (a := rawBits w n))

private theorem previous (w : Window) {n i : Nat} (bound : i < n) :
    (table w n).getD i (false,false) = rawBits w i := by
  rw [List.getD_eq_getElem?_getD,earlier w bound]
  rfl

private theorem ordinaryArgument (w : Window) {raw h a : Nat}
    (read : unpackNode raw = some (4,[h,a]))
    (approved : (rawBits w raw).1 = true) : (rawBits w a).2 = true := by
  have small := (nodeBounds read).2 a (by simp)
  have output : (rawBits w raw).1 = termParts w (table w raw) 4 [h,a] := by
    simp only [rawBits,termNext,read,Option.any_some]
  have exactRow : (rawBits w raw).1 =
      (w.2.contains h && ((table w raw).getD a (false,false)).2) := output
  rw [exactRow,previous w small] at approved
  exact (Bool.and_eq_true_iff.mp approved).2

private theorem fromSingleton (w : Window) (q : Nat)
    (approved : (rawBits w (pair q 0 + 1)).2 = true) : (rawBits w q).1 = true := by
  let n := pair q 0
  have split : decode n = some (q,0) := encodedPair q 0
  obtain ⟨_,smallQ,smallNil⟩ := decoded split
  change (decode n).any (fun t =>
    ((table w (n+1)).getD t.1 (false,false)).1 &&
      ((table w (n+1)).getD t.2 (false,false)).2) = true at approved
  rw [split,Option.any_some,previous w (Nat.lt_succ_of_le smallQ)] at approved
  exact (Bool.and_eq_true_iff.mp approved).1

/-- Exact numeric chain on the original raw admission table, not a
reflection lemma for either actual typed window graph. -/
theorem exact_CoverOrdinarySingletonSourceType (s : Settings) (ctx raw h q ty : Nat)
    (read : unpackNode raw = some (4,[h,pair q 0 + 1]))
    (leaf : unpackNode q = some (3,[ty]))
    (positive : intrinsicWindow s ctx raw ≠ 0) : ty ∈ s.window.1 := by
  have yes : packedWindow s ctx (intrinsicType raw) raw = true := by
    cases matched : packedWindow s ctx (intrinsicType raw) raw
    · exact False.elim (positive (by simp [intrinsicWindow,matched]))
    · rfl
  cases hc : unpack ctx with
  | none => simp [packedWindow,hc] at yes
  | some c =>
    have source : admitted s c (intrinsicType raw) raw = true := by
      simpa only [packedWindow,hc,Option.any_some] using yes
    rw [admitted,Bool.and_eq_true] at source
    have good := source.2
    change ((NumberedWindowSyntaxAlgorithm.syntaxBits raw).1 && (rawBits s.window raw).1) = true at good
    have arg := ordinaryArgument s.window read (Bool.and_eq_true_iff.mp good).2
    have result := fromSingleton s.window q arg
    have readType : (rawBits s.window q).1 = s.window.1.contains ty := by
      simp only [rawBits,termNext,leaf,Option.any_some,termParts] <;> rfl
    rw [readType] at result
    exact List.contains_iff_mem.mp result

#print axioms exact_CoverOrdinarySingletonSourceType

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSingletonTypeAdmissionProof
