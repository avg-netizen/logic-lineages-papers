module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof

/-- The unpaired tail is at most the predecessor of the current nonzero code.
Thus the original numeric fuel budget covers every raw input. -/
theorem parserTotality (fuel value : Nat) (h : value < fuel) :
    ∃ xs : List Nat, numbersParse fuel value = some xs := by
  induction fuel generalizing value with
  | zero => omega
  | succ fuel ih =>
    cases value with
    | zero => exact ⟨[], rfl⟩
    | succ value =>
      have ht := Nat.unpair_right_le value
      obtain ⟨xs, hxs⟩ := ih (Nat.unpair value).2 (by omega)
      refine ⟨(Nat.unpair value).1 :: xs, ?_⟩
      simp only [numbersParse, hxs, Option.map_some]

theorem actualNaturalListParserTotality :
    NumberedMultisetNumericTotalityTargets.ActualNaturalListParserTotality :=
  parserTotality

theorem decoderTotality (value : Nat) :
    ∃ xs : List Nat, decodeNumbers value = some xs :=
  parserTotality (value + 1) value (by omega)

theorem actualNaturalListUniqueDecoding :
    NumberedMultisetNumericTotalityTargets.ActualNaturalListUniqueDecoding := by
  intro value
  obtain ⟨xs, hxs⟩ := decoderTotality value
  refine ⟨xs, hxs, ?_⟩
  intro ys hys
  exact Option.some.inj (hys.symm.trans hxs)

theorem encodingInjective : Function.Injective numbersNumber := by
  intro xs ys h
  have he : (some xs : Option (List Nat)) = some ys := by
    calc
      some xs = decodeNumbers (numbersNumber xs) := (numbersRoundTrip xs).symm
      _ = decodeNumbers (numbersNumber ys) := congrArg decodeNumbers h
      _ = some ys := numbersRoundTrip ys
  exact Option.some.inj he

theorem encodingSurjective : Function.Surjective numbersNumber := by
  intro value
  obtain ⟨xs, hxs⟩ := decoderTotality value
  exact ⟨xs, numbersSound value xs hxs⟩

theorem actualNaturalListEncodingBijection :
    NumberedMultisetNumericTotalityTargets.ActualNaturalListEncodingBijection :=
  ⟨encodingInjective, encodingSurjective⟩

theorem actualNaturalListDecoderEquation :
    NumberedMultisetNumericTotalityTargets.ActualNaturalListDecoderEquation := by
  intro value xs
  constructor
  · exact numbersSound value xs
  · intro h
    rw [← h]
    exact numbersRoundTrip xs

theorem encodedLengthBound (xs : List Nat) : xs.length ≤ numbersNumber xs := by
  induction xs with
  | nil => exact Nat.le_refl 0
  | cons head tail ih =>
    have ht := Nat.right_le_pair head (numbersNumber tail)
    simp only [List.length_cons, numbersNumber]
    omega

theorem encodedEntryBound (xs : List Nat) :
    ∀ entry ∈ xs, entry < numbersNumber xs := by
  induction xs with
  | nil => intro entry h; cases h
  | cons head tail ih =>
    intro entry h
    rcases List.mem_cons.mp h with heq | htail
    · subst entry
      have hh := Nat.left_le_pair head (numbersNumber tail)
      change head < 1 + Nat.pair head (numbersNumber tail)
      omega
    · have he := ih entry htail
      have ht := Nat.right_le_pair head (numbersNumber tail)
      change entry < 1 + Nat.pair head (numbersNumber tail)
      omega

theorem actualNaturalListCodeBounds :
    NumberedMultisetNumericTotalityTargets.ActualNaturalListCodeBounds :=
  fun xs => ⟨encodedLengthBound xs, encodedEntryBound xs⟩

/-- Bounds for the actual list returned at an arbitrary source code. -/
theorem decodedBounds (value : Nat) (xs : List Nat)
    (h : decodeNumbers value = some xs) :
    xs.length ≤ value ∧ ∀ entry ∈ xs, entry < value := by
  have he := numbersSound value xs h
  simpa only [he] using actualNaturalListCodeBounds xs

theorem parseCons (fuel head : Nat) (tail : List Nat) :
    numbersParse (fuel + 1) (numbersNumber (head :: tail)) =
      (numbersParse fuel (numbersNumber tail)).map (head :: ·) := by
  simp only [numbersNumber, Nat.add_comm 1, numbersParse, Nat.unpair_pair]

/-- The original parser consumes one unit per cons and one at the final nil. -/
theorem parseEncodedExactFuel (xs : List Nat) (fuel : Nat) :
    numbersParse fuel (numbersNumber xs) = some xs ↔ xs.length < fuel := by
  induction xs generalizing fuel with
  | nil =>
    cases fuel with
    | zero => simp [numbersParse]
    | succ fuel => simp [numbersNumber, numbersParse]
  | cons head tail ih =>
    cases fuel with
    | zero => simp [numbersParse]
    | succ fuel =>
      rw [parseCons]
      have hm :
          (numbersParse fuel (numbersNumber tail)).map (head :: ·) = some (head :: tail) ↔
            numbersParse fuel (numbersNumber tail) = some tail := by
        cases numbersParse fuel (numbersNumber tail) <;> simp
      simpa using hm.trans (ih fuel)

theorem actualNaturalListParserEquation :
    NumberedMultisetNumericTotalityTargets.ActualNaturalListParserEquation := by
  intro fuel value xs
  constructor
  · intro h
    have he := numbersParseSound fuel value xs h
    refine ⟨he, (parseEncodedExactFuel xs fuel).mp ?_⟩
    rw [he]
    exact h
  · rintro ⟨he, hf⟩
    rw [← he]
    exact (parseEncodedExactFuel xs fuel).mpr hf

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTotalityProof
