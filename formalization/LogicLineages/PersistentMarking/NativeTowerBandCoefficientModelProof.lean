import LogicLineages.PersistentMarking.NativeTowerVariableDimensionBandsProof
import Init.Data.List.Lex

namespace LogicLineages.PersistentMarking.NativeTowerBandCoefficientModelProof
open NativeTowerNestedInnerOrbitLexProof NativeTowerVariableDimensionBandsProof

/-- A nonempty, big-endian finite coefficient list with no leading zero.
Trailing and internal zero coefficients are unchanged. -/
def PositiveLeading : List Nat → Prop
  | [] => False
  | a :: _ => 0 < a

def PositiveCoefficients := {xs : List Nat // PositiveLeading xs}

def coeffs : (d : Nat) → OrbitCoords d → List Nat
  | 0, p => [Nat.succ p]
  | d+1, p => coeffs d p.1 ++ [p.2]

theorem coeffsLength (d : Nat) : ∀ p : OrbitCoords d, (coeffs d p).length = d+1 := by
  induction d with
  | zero => intro p; rfl
  | succ d ih =>
    intro p
    simp only [coeffs,List.length_append,List.length_cons,List.length_nil,ih]

private theorem keepLeading (xs : List Nat) (a : Nat) (h : PositiveLeading xs) :
    PositiveLeading (xs ++ [a]) := by
  cases xs with
  | nil => exact False.elim h
  | cons x xs => exact h

theorem coeffsLeading (d : Nat) : ∀ p : OrbitCoords d, PositiveLeading (coeffs d p) := by
  induction d with
  | zero => intro p; exact Nat.zero_lt_succ p
  | succ d ih => intro p; exact keepLeading (coeffs d p.1) p.2 (ih p.1)

private theorem coeffsInjective (d : Nat) : ∀ p q : OrbitCoords d, coeffs d p = coeffs d q → p = q := by
  induction d with
  | zero =>
    intro p q h
    change [Nat.succ p] = [Nat.succ q] at h
    exact Nat.succ.inj (List.cons.inj h).1
  | succ d ih =>
    intro p q h
    change coeffs d p.1 ++ [p.2] = coeffs d q.1 ++ [q.2] at h
    obtain ⟨first,last⟩ := List.append_singleton_inj.mp h
    exact Prod.ext (ih p.1 q.1 first) last

def toCoefficients (p : BandCoords) : PositiveCoefficients :=
  ⟨coeffs p.1 p.2,coeffsLeading p.1 p.2⟩

def appendCoord (p : BandCoords) (n : Nat) : BandCoords :=
  ⟨p.1+1,(p.2,n)⟩

def ofCoefficients : PositiveCoefficients → BandCoords
  | ⟨[],positive⟩ => False.elim positive
  | ⟨a :: rest,_⟩ => rest.foldl appendCoord ⟨0,a-1⟩

private theorem appendedCoefficients (rest : List Nat) :
    ∀ p : BandCoords, (toCoefficients (rest.foldl appendCoord p)).val =
      (toCoefficients p).val ++ rest := by
  induction rest with
  | nil => intro p; simp
  | cons n rest ih =>
    intro p
    rw [List.foldl_cons,ih]
    change ((toCoefficients p).val ++ [n]) ++ rest = (toCoefficients p).val ++ n :: rest
    rw [List.append_assoc] <;> rfl

theorem exact_OriginalBandCoefficientDecode (q : PositiveCoefficients) :
    toCoefficients (ofCoefficients q) = q := by
  apply Subtype.ext
  rcases q with ⟨xs,positive⟩
  cases xs with
  | nil => exact False.elim positive
  | cons a rest =>
    change (toCoefficients (rest.foldl appendCoord ⟨0,a-1⟩)).val = a :: rest
    rw [appendedCoefficients]
    change Nat.succ (a-1) :: rest = a :: rest
    have actual : 0 < a := positive
    have leading : Nat.succ (a-1) = a := by omega
    rw [leading]

theorem exact_OriginalBandCoefficientInjective :
    ∀ p q : BandCoords, toCoefficients p = toCoefficients q → p = q := by
  intro p q h
  rcases p with ⟨d,p⟩
  rcases q with ⟨e,q⟩
  have lists : coeffs d p = coeffs e q := congrArg Subtype.val h
  have lengths := congrArg List.length lists
  rw [coeffsLength,coeffsLength] at lengths
  have same : d = e := Nat.succ.inj lengths
  subst e
  have eq := coeffsInjective d p q lists
  cases eq
  rfl

theorem exact_OriginalBandCoefficientEncode (p : BandCoords) :
    ofCoefficients (toCoefficients p) = p :=
  exact_OriginalBandCoefficientInjective _ _ (exact_OriginalBandCoefficientDecode _)

private theorem lexAppend {xs ys : List Nat} {a b : Nat} (size : xs.length = ys.length) :
    List.Lex Nat.lt (xs ++ [a]) (ys ++ [b]) ↔
      List.Lex Nat.lt xs ys ∨ (xs = ys ∧ a < b) := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => simp [List.cons_lex_cons_iff]
    | cons y ys => cases size
  | cons x xs ih =>
    cases ys with
    | nil => cases size
    | cons y ys =>
      have tails : xs.length = ys.length := Nat.succ.inj size
      simp only [List.cons_append,List.cons_lex_cons_iff,ih tails,List.cons.injEq]
      constructor
      · rintro (lt | ⟨eq,(early | ⟨same,last⟩)⟩)
        · exact Or.inl (Or.inl lt)
        · exact Or.inl (Or.inr ⟨eq,early⟩)
        · exact Or.inr ⟨⟨eq,same⟩,last⟩
      · rintro ((lt | ⟨eq,early⟩) | ⟨⟨eq,same⟩,last⟩)
        · exact Or.inl lt
        · exact Or.inr ⟨eq,Or.inl early⟩
        · exact Or.inr ⟨eq,Or.inr ⟨same,last⟩⟩

theorem exact_OriginalOrbitCoefficientDictionary (d : Nat) :
    ∀ (p q : OrbitCoords d), OrbitLex d p q ↔ List.Lex Nat.lt (coeffs d p) (coeffs d q) := by
  induction d with
  | zero =>
    intro p q
    change Nat.lt p q ↔ List.Lex Nat.lt [Nat.succ p] [Nat.succ q]
    simp only [List.cons_lex_cons_iff,List.not_lex_nil,and_false,or_false]
    exact ⟨Nat.succ_lt_succ,Nat.lt_of_succ_lt_succ⟩
  | succ d ih =>
    intro p q
    change (OrbitLex d p.1 q.1 ∨ (p.1 = q.1 ∧ p.2 < q.2)) ↔
      List.Lex Nat.lt (coeffs d p.1 ++ [p.2]) (coeffs d q.1 ++ [q.2])
    have sizes : (coeffs d p.1).length = (coeffs d q.1).length := by rw [coeffsLength,coeffsLength]
    have same : coeffs d p.1 = coeffs d q.1 ↔ p.1 = q.1 :=
      ⟨coeffsInjective d p.1 q.1,congrArg (coeffs d)⟩
    rw [lexAppend sizes,same,ih p.1 q.1]

/-- Standard length, then lexicographic dictionary order on big-endian
coefficients. No value or rank of a named ordinal is used. -/
def coefficientStrict (x y : PositiveCoefficients) : Prop :=
  x.val.length < y.val.length ∨
    (x.val.length = y.val.length ∧ List.Lex Nat.lt x.val y.val)

theorem exact_OriginalBandCoefficientStrictIff (p q : BandCoords) :
    BandLex p q ↔ coefficientStrict (toCoefficients p) (toCoefficients q) := by
  rcases p with ⟨d,p⟩
  rcases q with ⟨e,q⟩
  change (d < e ∨ ∃ same : d = e, OrbitLex d p (cast (congrArg OrbitCoords same.symm) q)) ↔
    ((coeffs d p).length < (coeffs e q).length ∨
      ((coeffs d p).length = (coeffs e q).length ∧ List.Lex Nat.lt (coeffs d p) (coeffs e q)))
  rw [coeffsLength,coeffsLength]
  constructor
  · rintro (earlier | ⟨same,inside⟩)
    · exact Or.inl (Nat.succ_lt_succ earlier)
    · subst e
      exact Or.inr ⟨rfl,(exact_OriginalOrbitCoefficientDictionary d p q).mp inside⟩
  · rintro (earlier | ⟨same,inside⟩)
    · exact Or.inl (Nat.lt_of_succ_lt_succ earlier)
    · have dim : d = e := Nat.succ.inj same
      subst e
      exact Or.inr ⟨rfl,(exact_OriginalOrbitCoefficientDictionary d p q).mpr inside⟩

#print axioms coeffsLength
#print axioms exact_OriginalBandCoefficientDecode
#print axioms exact_OriginalBandCoefficientInjective
#print axioms exact_OriginalBandCoefficientEncode
#print axioms exact_OriginalOrbitCoefficientDictionary
#print axioms exact_OriginalBandCoefficientStrictIff

end LogicLineages.PersistentMarking.NativeTowerBandCoefficientModelProof
