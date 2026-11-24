module
public import LogicLineages.PersistentMarking.NumberedWindowFieldAlgorithm

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
open NumberedWindowFieldAlgorithm (unpackNode)

def row (prior : List Nat) (tag : Nat) (xs : List Nat) : Nat :=
  if tag = 0 ∧ xs.length = 2 then 2 else
  if tag = 3 ∧ xs.length = 1 then 1 else
  if tag = 6 ∧ xs.length = 4 then
    let child := prior.getD (xs.getD 2 0) 0
    if child = 0 then 0 else child+1
  else 0

def next (n : Nat) (prior : List Nat) : Nat :=
  ((unpackNode n).map (fun q => row prior q.1 q.2)).getD 0

def table : Nat → List Nat
  | 0 => []
  | n+1 => let xs := table n; xs ++ [next n xs]

/-- Zero rejects. A nonzero value is one plus the true original left
spine rank, so the accepting value on bare bottom is one. -/
def rawRank (n : Nat) : Nat := next n (table n)

theorem tableLength (n : Nat) : (table n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

theorem tableEarlier (i n : Nat) (h : i < n) : (table n).getD i 0 = rawRank i := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hi : i < n
    · have old : i < (table n).length := by simpa only [tableLength] using hi
      rw [table,List.getD_eq_getElem?_getD,List.getElem?_append_left old]
      rw [← List.getD_eq_getElem?_getD]
      exact ih hi
    · have eq : i = n := by omega
      subst i
      rw [table,List.getD_eq_getElem?_getD,List.getElem?_append_right (by rw [tableLength]; exact Nat.le_refl n),
        tableLength,Nat.sub_self]
      rfl

end LogicLineages.PersistentMarking.NumberedWindowNeutralSpineRankAlgorithm
