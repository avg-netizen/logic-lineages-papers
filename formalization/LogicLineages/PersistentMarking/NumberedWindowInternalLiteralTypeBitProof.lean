module

public import LogicLineages.PersistentMarking.NumberedWindowAddressAlgorithm
public import LogicLineages.PersistentMarking.NumberedWindowAnnotationAlgorithm
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserRawPairProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeBitProof
open NumberedWindowAddressAlgorithm (nextType typeTable typeBit)
open NumberedWindowPairAlgorithm (pair)
open NumberedWindowAnnotationAlgorithm (arrow)
open NumberedWindowInternalSparseFieldParserRawPairProof (encodedPair tailBound)

private theorem tableLength (n : Nat) : (typeTable n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [typeTable,ih]

private theorem earlier {n i : Nat} (bound : i < n) :
    (typeTable n)[i]? = some (typeBit i) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases prior : i < n
    · simp only [typeTable,List.getElem?_append_left (tableLength n ▸ prior)]
      exact ih prior
    · have last : i = n := by omega
      subst i
      change (typeTable n ++ [typeBit n])[n]? = some (typeBit n)
      simpa only [tableLength] using
        (List.getElem?_concat_length (l := typeTable n) (a := typeBit n))

private theorem previous {n i : Nat} (bound : i < n) :
    (typeTable n).getD i false = typeBit i := by
  rw [List.getD_eq_getElem?_getD,earlier bound]
  rfl

theorem exact_LiteralTypeBitArrow (dom cod : Nat) :
    typeBit (arrow dom cod) = (typeBit dom && typeBit cod) := by
  have domainBound : dom < pair dom cod + 1 := by
    have le : dom ≤ pair dom cod := by
      unfold pair
      omega
    omega
  have codomainBound : cod < pair dom cod + 1 :=
    Nat.lt_succ_of_le (tailBound dom cod)
  change nextType (pair dom cod + 1) (typeTable (pair dom cod + 1)) = _
  rw [nextType,encodedPair]
  change ((typeTable (pair dom cod + 1)).getD dom false &&
    (typeTable (pair dom cod + 1)).getD cod false) = _
  rw [previous domainBound,previous codomainBound]

#print axioms exact_LiteralTypeBitArrow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypeBitProof
