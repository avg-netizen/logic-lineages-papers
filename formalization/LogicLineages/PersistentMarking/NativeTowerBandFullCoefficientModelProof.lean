import LogicLineages.PersistentMarking.NativeTowerBandCoefficientModelProof

namespace LogicLineages.PersistentMarking.NativeTowerBandFullCoefficientModelProof
open NativeTowerBandCoefficientModelProof

/-- Empty is exactly zero; all nonempty representations retain a positive
leading coefficient. In particular [0] is not admitted. -/
def FullLeading : List Nat → Prop
  | [] => True
  | a :: _ => 0 < a

def FullCoefficients := {xs : List Nat // FullLeading xs}

def fullStrict (x y : FullCoefficients) : Prop :=
  x.val.length < y.val.length ∨
    (x.val.length = y.val.length ∧ List.Lex Nat.lt x.val y.val)

/-- Absorb zero only in the one-coefficient band, by its ordinary successor
shift. All longer coefficient words stay literal. -/
def raiseZero : List Nat → List Nat
  | [] => [1]
  | [a] => [Nat.succ a]
  | a :: b :: rest => a :: b :: rest

def lowerZero : List Nat → List Nat
  | [a] => if a = 1 then [] else [a-1]
  | xs => xs

private theorem raisedPositive (xs : List Nat) (h : FullLeading xs) :
    PositiveLeading (raiseZero xs) := by
  cases xs with
  | nil => exact Nat.zero_lt_succ 0
  | cons a rest =>
    cases rest with
    | nil => exact Nat.zero_lt_succ a
    | cons b rest => exact h

private theorem loweredFull (xs : List Nat) (h : PositiveLeading xs) :
    FullLeading (lowerZero xs) := by
  cases xs with
  | nil => exact False.elim h
  | cons a rest =>
    cases rest with
    | nil =>
      change FullLeading (if a = 1 then [] else [a-1])
      split
      · trivial
      · change 0 < a at h
        change 0 < a-1
        omega
    | cons b rest => exact h

def raiseFull (x : FullCoefficients) : PositiveCoefficients :=
  ⟨raiseZero x.val,raisedPositive x.val x.property⟩

def lowerPositive (x : PositiveCoefficients) : FullCoefficients :=
  ⟨lowerZero x.val,loweredFull x.val x.property⟩

theorem exact_FullCoefficientLeftInverse (x : FullCoefficients) :
    lowerPositive (raiseFull x) = x := by
  apply Subtype.ext
  rcases x with ⟨xs,h⟩
  change lowerZero (raiseZero xs) = xs
  cases xs with
  | nil => rfl
  | cons a rest =>
    cases rest with
    | nil =>
      change (if Nat.succ a = 1 then [] else [Nat.succ a - 1]) = [a]
      change 0 < a at h
      have different : Nat.succ a ≠ 1 := by omega
      rw [if_neg different]
      simp
    | cons b rest => rfl

theorem exact_FullCoefficientRightInverse (x : PositiveCoefficients) :
    raiseFull (lowerPositive x) = x := by
  apply Subtype.ext
  rcases x with ⟨xs,h⟩
  change raiseZero (lowerZero xs) = xs
  cases xs with
  | nil => exact False.elim h
  | cons a rest =>
    cases rest with
    | nil =>
      change raiseZero (if a = 1 then [] else [a-1]) = [a]
      by_cases one : a = 1
      · subst a
        rfl
      · rw [if_neg one]
        change [Nat.succ (a-1)] = [a]
        change 0 < a at h
        have exactNat : Nat.succ (a-1) = a := by omega
        rw [exactNat]
    | cons b rest => rfl

private theorem singletonLex (a b : Nat) :
    List.Lex Nat.lt [a] [b] ↔ a < b := by
  simp only [List.cons_lex_cons_iff,List.not_lex_nil,and_false,or_false] <;> rfl

private theorem compare (xs ys : List Nat) (hx : FullLeading xs) (hy : FullLeading ys) :
    (xs.length < ys.length ∨ (xs.length = ys.length ∧ List.Lex Nat.lt xs ys)) ↔
    ((raiseZero xs).length < (raiseZero ys).length ∨
      ((raiseZero xs).length = (raiseZero ys).length ∧ List.Lex Nat.lt (raiseZero xs) (raiseZero ys))) := by
  cases xs with
  | nil =>
    cases ys with
    | nil =>
      simp [raiseZero,List.not_lex_nil,singletonLex]
    | cons b bs =>
      cases bs with
      | nil =>
        change 0 < b at hy
        simp [raiseZero,singletonLex,show 1 < Nat.succ b from Nat.succ_lt_succ hy]
      | cons c cs =>
        have big : 1 < (b :: c :: cs).length := by
          simp only [List.length_cons]
          omega
        have nonempty : 0 < (b :: c :: cs).length := Nat.lt_trans (by decide) big
        simpa only [raiseZero,List.length_nil,List.length_singleton,nonempty,big,true_or]
  | cons a as =>
    cases as with
    | nil =>
      cases ys with
      | nil =>
        have notLt : ¬ Nat.succ a < 1 :=
          Nat.not_lt_of_ge (Nat.succ_le_succ (Nat.zero_le a))
        simp [raiseZero,singletonLex,notLt]
      | cons b bs =>
        cases bs with
        | nil =>
          simp only [raiseZero,List.length_singleton,Nat.lt_irrefl,false_or,true_and,singletonLex]
          exact ⟨Nat.succ_lt_succ,Nat.lt_of_succ_lt_succ⟩
        | cons c cs =>
          have big : 1 < (b :: c :: cs).length := by
            simp only [List.length_cons]
            omega
          simp only [raiseZero,List.length_singleton,big,true_or]
    | cons b bs =>
      cases ys with
      | nil =>
        have big : 1 < (a :: b :: bs).length := by
          simp only [List.length_cons]
          omega
        have notLt : ¬ (a :: b :: bs).length < 1 := Nat.not_lt_of_ge (Nat.le_of_lt big)
        have unequal : (a :: b :: bs).length ≠ 1 := by omega
        have nonempty : 0 < (a :: b :: bs).length := Nat.lt_trans (by decide) big
        have notZero : ¬ (a :: b :: bs).length < 0 := Nat.not_lt_zero _
        have unequalZero : (a :: b :: bs).length ≠ 0 := by omega
        simp only [raiseZero,List.length_nil,List.length_singleton,notLt,unequal,
          notZero,unequalZero,false_and,false_or]
      | cons c cs =>
        cases cs with
        | nil =>
          have big : 1 < (a :: b :: bs).length := by
            simp only [List.length_cons]
            omega
          have notLt : ¬ (a :: b :: bs).length < 1 := Nat.not_lt_of_ge (Nat.le_of_lt big)
          have unequal : (a :: b :: bs).length ≠ 1 := by omega
          simp only [raiseZero,List.length_singleton,notLt,unequal,false_and,false_or]
        | cons d ds => rfl

theorem exact_FullCoefficientStrictIff (x y : FullCoefficients) :
    fullStrict x y ↔ coefficientStrict (raiseFull x) (raiseFull y) :=
  compare x.val y.val x.property y.property

theorem exact_FullCoefficientZeroAndLong :
    (raiseFull ⟨[],True.intro⟩).val = [1] ∧
    (∀ a (h : 0 < a), (raiseFull ⟨[a],h⟩).val = [Nat.succ a]) ∧
    (∀ a b rest (h : 0 < a),
      (raiseFull ⟨a :: b :: rest,h⟩).val = a :: b :: rest) :=
  ⟨rfl,fun _ _ => rfl,fun _ _ _ _ => rfl⟩

#print axioms exact_FullCoefficientLeftInverse
#print axioms exact_FullCoefficientRightInverse
#print axioms exact_FullCoefficientStrictIff
#print axioms exact_FullCoefficientZeroAndLong

end LogicLineages.PersistentMarking.NativeTowerBandFullCoefficientModelProof
