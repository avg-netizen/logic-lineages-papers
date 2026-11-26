module
public import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesTargets
import LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesCodecProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesExchangeTableProof
open NumberedWindowPairAlgorithm (pair decode)
open NumberedWindowCoverBoundsAlgorithm (bounds)
open NumberedWindowExchangeAtoms (HeadPairs)
open NumberedWindowExchangeAlgorithm (table next row termNext argsNext)
open NumberedWindowRawExchangeVerticesCodecProof (decoded samePair childKeyLt)

def BoundAgreement (hp : HeadPairs) (a b : Nat) : Prop :=
  ((row hp a b).1 = true → (bounds a).1 = (bounds b).1) ∧
  ((row hp a b).2 = true → (bounds a).2 = (bounds b).2)

/-- These coordinates are the strictly earlier actual raw pair keys,
not lexicographic comparisons of decoded terms or of annotations. -/
def EarlierAgreement (hp : HeadPairs) (a b : Nat) : Prop :=
  ∀ x y, pair x y < pair a b → BoundAgreement hp x y

private theorem tableLength (hp : HeadPairs) (n : Nat) : (table hp n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem earlier (hp : HeadPairs) {k n : Nat} (order : k < n) :
    (table hp n)[k]? = some (next hp (table hp k) k) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases before : k < n
    · simp only [table,List.getElem?_append_left (tableLength hp n ▸ before)]
      exact ih before
    · obtain rfl : k = n := by omega
      simpa only [table,tableLength] using
        (List.getElem?_concat_length (l := table hp k) (a := next hp (table hp k) k))

private theorem earlierRow (hp : HeadPairs) {x y a b : Nat}
    (h : pair x y < pair a b) :
    (table hp (pair a b)).getD (pair x y) (false,false) = row hp x y := by
  rw [List.getD_eq_getElem?_getD,earlier hp h]
  rfl

/-- On a successful row, the physically selected decode must be the
claimed original pair. No alternate decoder completion is used. -/
theorem successfulView (hp : HeadPairs) (a b : Nat)
    (h : (row hp a b).1 = true ∨ (row hp a b).2 = true) :
    row hp a b = (termNext hp (table hp (pair a b)) a b,argsNext (table hp (pair a b)) a b) := by
  cases found : decode (pair a b) with
  | none => simp [row,next,found] at h
  | some p =>
    rcases p with ⟨x,y⟩
    obtain ⟨sameX,sameY⟩ := samePair (decoded found).1
    subst x
    subst y
    simp [row,next,found]

theorem earlierTerm (hp : HeadPairs) {a b x y : Nat}
    (inductionAt : EarlierAgreement hp a b) (hx : x < a) (hy : y < b)
    (h : ((table hp (pair a b)).getD (pair x y) (false,false)).1 = true) :
    (bounds x).1 = (bounds y).1 := by
  have key := childKeyLt hx (Nat.le_of_lt hy)
  rw [earlierRow hp key] at h
  exact (inductionAt x y key).1 h

theorem earlierArgs (hp : HeadPairs) {a b x y : Nat}
    (inductionAt : EarlierAgreement hp a b) (hx : x < a) (hy : y < b)
    (h : ((table hp (pair a b)).getD (pair x y) (false,false)).2 = true) :
    (bounds x).2 = (bounds y).2 := by
  have key := childKeyLt hx (Nat.le_of_lt hy)
  rw [earlierRow hp key] at h
  exact (inductionAt x y key).2 h

end LogicLineages.PersistentMarking.NumberedWindowRawExchangeVerticesExchangeTableProof
