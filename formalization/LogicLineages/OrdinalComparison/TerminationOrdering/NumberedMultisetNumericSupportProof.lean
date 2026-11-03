module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedMultisetCertificate NumberedMultisetNumeric

theorem numbersParseRoundTrip (xs : List Nat) : ∀ fuel,numbersNumber xs<fuel → numbersParse fuel (numbersNumber xs)=some xs := by
  induction xs with
  | nil => intro fuel h; cases fuel with
    | zero => omega
    | succ fuel => rfl
  | cons x xs ih =>
    intro fuel h
    cases fuel with
    | zero => omega
    | succ fuel =>
      have hb := Nat.right_le_pair x (numbersNumber xs)
      simp only [numbersNumber] at h
      have hf : numbersNumber xs<fuel := by omega
      rw [numbersNumber,Nat.add_comm 1]
      simp [numbersParse,ih fuel hf]

theorem numbersRoundTrip (xs : List Nat) : decodeNumbers (numbersNumber xs)=some xs :=
  numbersParseRoundTrip xs _ (by omega)

theorem numbersParseSound (fuel : Nat) : ∀ value xs,numbersParse fuel value=some xs → numbersNumber xs=value := by
  induction fuel with
  | zero => intro value xs h; cases h
  | succ fuel ih =>
    intro value xs h
    cases value with
    | zero => cases h; rfl
    | succ value =>
      simp only [numbersParse,Option.map_eq_some_iff] at h
      obtain ⟨rest,hr,rfl⟩ := h
      simp [numbersNumber,ih _ _ hr,Nat.add_comm]

theorem numbersSound (value : Nat) (xs : List Nat) (h : decodeNumbers value=some xs) : numbersNumber xs=value :=
  numbersParseSound (value+1) value xs h

theorem packedNumbersRoundTrip (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (qs : List (Packed (Fin n) arity Gamma)) :
    decodePackedNumbers n arity Gamma (qs.map packedNumber)=some qs := by
  induction qs with
  | nil => rfl
  | cons q qs ih =>
    have hq : decodePackedNumber n arity Gamma (packedNumber q)=some q :=
      NumberedNumericDecodingProof.packedNumericRoundTrip n arity Gamma q
    simp [decodePackedNumbers,hq,ih]

theorem packedNumbersSound (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (xs : List Nat) :
    ∀ qs,decodePackedNumbers n arity Gamma xs=some qs → qs.map packedNumber=xs := by
  induction xs with
  | nil => intro qs h; cases h; rfl
  | cons x xs ih =>
    intro qs h
    cases hq : decodePackedNumber n arity Gamma x with
    | none => simp [decodePackedNumbers,hq] at h
    | some q =>
      cases hr : decodePackedNumbers n arity Gamma xs with
      | none => simp [decodePackedNumbers,hq,hr] at h
      | some rest =>
        simp only [decodePackedNumbers,hq,hr,Option.bind_some,Option.some.injEq] at h
        cases h
        have he := NumberedNumericDecodingProof.packedNumericSound n arity Gamma x q hq
        simp [he,ih rest hr]

theorem packedRoundTrip (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (qs : List (Packed (Fin n) arity Gamma)) :
    decodePackedList n arity Gamma (packedListNumber qs)=some qs := by
  simp [decodePackedList,packedListNumber,numbersRoundTrip,packedNumbersRoundTrip]

theorem packedSound (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) (qs : List (Packed (Fin n) arity Gamma))
    (h : decodePackedList n arity Gamma value=some qs) : packedListNumber qs=value := by
  cases hn : decodeNumbers value with
  | none => simp [decodePackedList,hn] at h
  | some xs =>
    have hp : decodePackedNumbers n arity Gamma xs=some qs := by simpa [decodePackedList,hn] using h
    unfold packedListNumber
    rw [packedNumbersSound n arity Gamma xs qs hp]
    exact numbersSound value xs hn

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
