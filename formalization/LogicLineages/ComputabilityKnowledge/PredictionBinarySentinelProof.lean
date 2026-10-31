module
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelProof
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionBinarySentinel PredictionBinarySentinelTargets

private def posDigit (p : PosNum) (b : Bool) : PosNum := if b then p.bit1 else p.bit0

private theorem fold_cast (xs : List Bool) (p : PosNum) :
    ((xs.foldl posDigit p : PosNum) : Nat) = xs.foldl (fun n b => 2 * n + b.toNat) (p : Nat) := by
  induction xs generalizing p with
  | nil => rfl
  | cons b xs ih =>
    simp only [List.foldl_cons, ih]
    congr 1
    cases b <;> simp [posDigit, two_mul]

private theorem fold_bits (xs : List Bool) (p : PosNum) :
    trPosNum (xs.foldl posDigit p) = (xs.map bitSymbol).reverse ++ trPosNum p := by
  induction xs generalizing p with
  | nil => rfl
  | cons b xs ih =>
    rw [List.foldl_cons, ih]
    cases b <;> simp [posDigit, bitSymbol, trPosNum, List.reverse_cons, List.append_assoc]

theorem effectiveSentinel : EffectiveSentinel := by
  have hb : Primrec Bool.toNat := Primrec.dom_finite _
  exact Primrec.list_foldl Primrec.id (Primrec.const 1)
    ((Primrec.nat_add.comp
      (Primrec.nat_mul.comp (Primrec.const 2) (Primrec.fst.comp Primrec.snd))
      (hb.comp (Primrec.snd.comp Primrec.snd))).to₂)

theorem exactNaturalEncoding : ExactNaturalEncoding := by
  intro xs
  have hc : inputNat xs = ((xs.foldl posDigit PosNum.one : PosNum) : Nat) :=
    (fold_cast xs PosNum.one).symm
  rw [hc, trNat, PosNum.of_to_nat]
  exact fold_bits xs PosNum.one

private theorem work_map (g : Γ') :
    (Function.update (fun _ : K' => none) K'.main (some g)) = slots (some g) none none none := by
  funext k
  cases k <;> simp [slots, Function.update]

theorem exactInputLayout : ExactInputLayout := by
  intro xs
  have hn := exactNaturalEncoding xs
  simp only [PredictionCompilerFiniteExecution.sourceInput, trList, hn,
    List.append_nil, TM2to1.trInit, List.reverse_append, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.reverse_reverse, List.map_cons, List.map_map]
  change (true, (((Γ'.cons :: Γ'.bit1 :: xs.map bitSymbol).map
    (fun a : Γ' => (false, Function.update (fun _ : K' => none) K'.main (some a)))).headI).2) ::
    (((Γ'.cons :: Γ'.bit1 :: xs.map bitSymbol).map
      (fun a : Γ' => (false, Function.update (fun _ : K' => none) K'.main (some a)))).tail) = _
  simp only [List.map_cons, List.headI_cons, List.tail_cons, List.map_map]
  simp only [work_map, bottomSymbol, rawSymbol, bitSymbol, Bool.true_eq, ↓reduceIte]
  rfl

theorem injectiveSentinel : InjectiveSentinel := by
  intro xs ys h
  have ht := congrArg trNat h
  rw [exactNaturalEncoding, exactNaturalEncoding] at ht
  have hm := List.reverse_injective (List.append_cancel_right ht)
  exact (List.map_injective_iff.2 (by intro a b hab; cases a <;> cases b <;> simp_all [bitSymbol])) hm

theorem exactBinarySlots : ExactBinarySlots := by
  have h0 : rawSymbol false ≠ (default : TapeAlphabet) := by
    intro h
    have := congrArg (fun a : TapeAlphabet => a.2 K'.main) h
    cases this
  have h1 : rawSymbol true ≠ (default : TapeAlphabet) := by
    intro h
    have := congrArg (fun a : TapeAlphabet => a.2 K'.main) h
    cases this
  have h01 : rawSymbol false ≠ rawSymbol true := by
    intro h
    have := congrArg (fun a : TapeAlphabet => a.2 K'.main) h
    cases this
  refine ⟨?_, ?_, h0, h1, h01⟩
  · simp [rawIndex, PredictionFiniteRenaming.index, PredictionFiniteRenaming.items,
      binaryAlphabetTail, h0, Ne.symm h0]
  · simp [rawIndex, PredictionFiniteRenaming.index, PredictionFiniteRenaming.items,
      binaryAlphabetTail, h1, Ne.symm h1, h01, Ne.symm h01]

end LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelProof
