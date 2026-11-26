module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTargets

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
open NumberedWindowCoverBoundsAlgorithm (table bounds termNext termMeasure)
open NumberedWindowFieldAlgorithm (unpackNode)

private theorem tableLength (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem lookup {i n : Nat} (h : i < n) : (table n)[i]? = some (bounds i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases before : i < n
    · simp only [table,List.getElem?_append_left (tableLength n ▸ before)]
      exact ih before
    · have last : i = n := by omega
      subst i
      change (table n ++ [bounds n])[n]? = some (bounds n)
      simpa only [tableLength] using
        (List.getElem?_concat_length (l := table n) (a := bounds n))

theorem previous {i n : Nat} (h : i < n) :
    (table n).getD i default = bounds i := by
  rw [List.getD_eq_getElem?_getD,lookup h]
  rfl

theorem termBounds {n tag : Nat} {xs : List Nat} (read : unpackNode n = some (tag,xs)) :
    (bounds n).1 = termMeasure (table n) tag xs := by
  simp [bounds,termNext,read]

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesBoundsTableProof
