import LogicLineages.PersistentMarking.NumberedWindowArithmeticExchangeTargets
import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks

namespace LogicLineages.PersistentMarking.NumberedWindowExchangeTableProof
open NumberedWindowExchangeAlgorithm NumberedWindowExchangeAtoms NumberedWindowPairAlgorithm (pair)
open NumberedWindowArithmeticFields (encodeNode)
open NumberedWindowArithmeticNodeProof (nodeRound nodeBelow)
open NumberedWindowArithmeticCodecLaws (pairRound pairBounds)

private theorem lengthTable (hp : HeadPairs) (n : Nat) : (table hp n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier (hp : HeadPairs) {k n : Nat} (h : k<n) :
    (table hp n)[k]? = some (next hp (table hp k) k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases lt : k<n
    · simp only [table,List.getElem?_append_left (lengthTable hp n ▸ lt)]
      exact ih lt
    · obtain rfl : k=n := by omega
      simpa only [table,lengthTable] using
        (List.getElem?_concat_length (l := table hp k) (a := next hp (table hp k) k))

private theorem keyLt {x y a b : Nat} (h : x<a) (k : y≤b) : pair x y < pair a b := by
  have s : x+y≤a+b := Nat.add_le_add (Nat.le_of_lt h) k
  exact Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul s s) h

theorem atChild (hp : HeadPairs) {a b x y : Nat} (hx : x<a) (hy : y<b) :
    (table hp (pair a b)).getD (pair x y) (false,false) = row hp x y := by
  rw [List.getD_eq_getElem?_getD,earlier hp (keyLt hx (Nat.le_of_lt hy))]
  rfl

theorem nodeChild (hp : HeadPairs) (i j : Nat) (fs gs : List Nat) (x y : Nat)
    (hx : x ∈ fs) (hy : y ∈ gs) :
    (table hp (pair (encodeNode i fs) (encodeNode j gs))).getD (pair x y) (false,false) = row hp x y :=
  atChild hp (nodeBelow i fs x hx) (nodeBelow j gs y hy)

theorem rowAt (hp : HeadPairs) (a b : Nat) : row hp a b =
    (termNext hp (table hp (pair a b)) a b,argsNext (table hp (pair a b)) a b) := by
  simp [row,next,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,
    ← NumberedWindowActualPairAlgorithmChecks.currentPair,pairRound]

theorem nodeTerm (hp : HeadPairs) (i j : Nat) (fs gs : List Nat) :
    (row hp (encodeNode i fs) (encodeNode j gs)).1 =
    parts hp (table hp (pair (encodeNode i fs) (encodeNode j gs))) i j fs gs := by
  rw [rowAt]
  simp [termNext,← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2,nodeRound]

theorem argsCons (hp : HeadPairs) (x u y v : Nat) :
    (row hp (pair x u+1) (pair y v+1)).2 =
    (((row hp x y).1 && u == v) || (x == y && (row hp u v).2)) := by
  have h1 := atChild hp (Nat.lt_succ_of_le (pairBounds x u).1) (Nat.lt_succ_of_le (pairBounds y v).1)
  have h2 := atChild hp (Nat.lt_succ_of_le (pairBounds x u).2) (Nat.lt_succ_of_le (pairBounds y v).2)
  change (row hp (NumberedWindowArithmeticPair.pair x u+1) (NumberedWindowArithmeticPair.pair y v+1)).2 = _
  rw [rowAt]
  simp [argsNext,← NumberedWindowActualPairAlgorithmChecks.currentDecoder,pairRound,h1,h2]

theorem argsNil (hp : HeadPairs) (a : Nat) :
    (row hp 0 a).2 = false ∧ (row hp a 0).2 = false := by
  cases a <;> simp [rowAt,argsNext]
end LogicLineages.PersistentMarking.NumberedWindowExchangeTableProof
