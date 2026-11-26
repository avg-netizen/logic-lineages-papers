import LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxPartsProof
import LogicLineages.PersistentMarking.NumberedWindowArithmeticTermCodeChecks
import LogicLineages.PersistentMarking.NumberedWindowArithmeticFieldAlgorithmChecks

namespace LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmProof
open NumberedWindowSyntax NumberedWindowSyntaxAlgorithm NumberedWindowArithmeticSyntaxAlgorithmTargets
open NumberedWindowArithmeticTermCode NumberedWindowArithmeticTermCodeChecks
open NumberedWindowArithmeticNodeProof NumberedWindowArithmeticCodecLaws
open NumberedWindowArithmeticFields

private theorem adequate {encode : α → Nat} {read : Nat → Option α} {fuelRead : Nat → Nat → Option α}
    (readIff : ∀ n x, read n = some x ↔ encode x = n)
    (sound : ∀ f c x, fuelRead f c = some x → encode x = c)
    (complete : ∀ f x, encode x ≤ f → fuelRead f (encode x) = some x)
    {c f : Nat} (hc : c ≤ f) : fuelRead f c = read c := by
  apply Option.ext
  intro x
  rw [readIff]
  constructor
  · exact sound f c x
  · intro h
    rw [← h] at hc ⊢
    exact complete f x hc

private theorem termFuel {i f : Nat} (h : i ≤ f) : decodeTermFuel f i = decodeTerm i :=
  adequate exact_TermCodec.1 exact_TermFuelCalibration.1 exact_TermFuelCalibration.2 h

private theorem argsFuel {i f : Nat} (h : i ≤ f) : decodeArgsFuel f i = decodeArgs i :=
  adequate exact_ArgsCodec.1 exact_ArgsFuelCalibration.1 exact_ArgsFuelCalibration.2 h

private theorem lookup {n i : Nat} (h : i < n) :
    ((List.range n).map OriginalRow).getD i (false,false) = OriginalRow i := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range h]

private theorem nextTerm (n : Nat) : termNext n ((List.range n).map OriginalRow) =
    (decodeTerm n).isSome := by
  cases n with
  | zero => rfl
  | succ m =>
    unfold termNext
    rw [← NumberedWindowArithmeticFieldAlgorithmChecks.exact_ExactTaggedNodeCodec.2]
    change _ = (decodeTermFuel (m+1) (m+1)).isSome
    simp only [decodeTermFuel]
    cases hd : decodeNode (m+1) with
    | none => rfl
    | some p =>
      rcases p with ⟨tag,fs⟩
      have hchild (i : Nat) (hi : i ∈ fs) : i < m+1 := by
        rw [← nodeRead hd]
        exact nodeBelow tag fs i hi
      apply NumberedWindowArithmeticSyntaxPartsProof.termShape
      · intro i hi
        rw [lookup (hchild i hi), termFuel (Nat.le_of_lt_succ (hchild i hi))]
        rfl
      · intro i hi
        rw [lookup (hchild i hi), argsFuel (Nat.le_of_lt_succ (hchild i hi))]
        rfl

private theorem nextArgs (n : Nat) : argsNext n ((List.range n).map OriginalRow) =
    (decodeArgs n).isSome := by
  cases n with
  | zero => rfl
  | succ m =>
    change _ = (decodeArgsFuel (m+1) (m+1)).isSome
    simp only [argsNext,decodeArgsFuel,← NumberedWindowActualPairAlgorithmChecks.currentDecoder]
    cases h : NumberedWindowArithmeticPair.decode m with
    | none => rfl
    | some pair =>
      rcases pair with ⟨q,r⟩
      have bounds := pairBounds q r
      rw [pairRead h] at bounds
      simp only [Option.any_some,Option.bind_eq_bind,Option.bind_some,lookup (Nat.lt_succ_of_le bounds.1),
        lookup (Nat.lt_succ_of_le bounds.2),OriginalRow,termFuel bounds.1,argsFuel bounds.2]
      cases decodeTerm q <;> cases decodeArgs r <;> rfl

theorem prefixTable : ExactTermArgsTable := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp [table, ih,List.range_succ,nextTerm,nextArgs,OriginalRow]

theorem guards : ExactTermArgsGuards := by
  intro n
  simpa [syntaxBits,prefixTable n,nextTerm,nextArgs,OriginalRow]

end LogicLineages.PersistentMarking.NumberedWindowArithmeticSyntaxAlgorithmProof
