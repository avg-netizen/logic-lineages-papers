module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryStepProof
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof
import LogicLineages.PersistentMarking.NumberedWindowAtomicApplicationTableProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryChecks

open NumberedWindowAtomicApplicationTableProof (rowAt)
open NumberedWindowExchangeAlgorithm (row bits next table)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowRawExchangeSymmetryStepProof
open NumberedWindowRawExchangeSymmetryTargets
open NumberedWindowRawExchangeVerticesCodecProof (childKeyLt)
open NumberedWindowScalarAlgorithm (edge)
open NumberedWindowSyntaxAlgorithm (syntaxBits)

private theorem tableLength (hp : HeadPairs) (n : Nat) : (table hp n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem tableEntry (hp : HeadPairs) {key n : Nat} (below : key < n) :
    (table hp n)[key]? = some (next hp (table hp key) key) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases earlier : key < n
    · simp only [table,List.getElem?_append_left (tableLength hp n ▸ earlier)]
      exact ih earlier
    · obtain rfl : key = n := by omega
      simpa only [table,tableLength] using
        (List.getElem?_concat_length (l := table hp key) (a := next hp (table hp key) key))

private theorem childRow (hp : HeadPairs) {a b x y : Nat} (hx : x < a) (hy : y < b) :
    (table hp (pair a b)).getD (pair x y) (false,false) = row hp x y := by
  rw [List.getD_eq_getElem?_getD,tableEntry hp (childKeyLt hx (Nat.le_of_lt hy))]
  rfl

theorem exact_RawRowSymmetry : ExactRawRowSymmetry := by
  intro hp symmetric
  have all : ∀ measure a b : Nat, a+b = measure → row hp a b = row hp b a := by
    intro measure
    induction measure using Nat.strongRecOn with
    | ind measure ih =>
      intro a b code
      have child : ChildRowsSymmetric hp a b := by
        intro x y hx hy
        rw [childRow hp hx hy,childRow hp hy hx]
        exact ih (x+y) (by omega) x y rfl
      rw [rowAt hp a b,rowAt hp b a]
      exact Prod.ext (termSymmetric hp symmetric a b child) (argsSymmetric hp a b child)
  intro a b
  exact all (a+b) a b rfl

theorem exact_RawExchangeSymmetry : ExactRawExchangeSymmetry := by
  intro hp symmetric a b
  have agreement := exact_RawRowSymmetry hp symmetric a b
  simp only [bits,agreement]
  apply Prod.ext
  · rw [Bool.and_comm (syntaxBits a).1 (syntaxBits b).1]
  · rw [Bool.and_comm (syntaxBits a).2 (syntaxBits b).2]

theorem exact_ScalarEdgeSymmetry : ExactScalarEdgeSymmetry := by
  intro s symmetric ctx ty a b
  have agreement := exact_RawExchangeSymmetry s.equivalentHeads symmetric a b
  simp only [edge,agreement,Bool.and_assoc]
  rw [Bool.and_comm (NumberedWindowScalarAlgorithm.admitted s ctx ty a)
    (NumberedWindowScalarAlgorithm.admitted s ctx ty b)]

#print axioms exact_RawRowSymmetry
#print axioms exact_RawExchangeSymmetry
#print axioms exact_ScalarEdgeSymmetry

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeSymmetryChecks
