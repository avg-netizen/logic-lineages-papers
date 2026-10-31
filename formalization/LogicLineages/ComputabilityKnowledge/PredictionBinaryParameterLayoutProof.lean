module
public import LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutTargets
public import LogicLineages.ComputabilityKnowledge.PredictionBinarySentinelProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutProof
open Turing Turing.PartrecToTM2 PredictionCompilerTapeSupport PredictionCompilerAlphabetEquality
open PredictionBinarySentinel PredictionBinaryParameterLayout PredictionBinaryParameterLayoutTargets

theorem bitsPrimitiveRecursive : BitsPrimitiveRecursive := by
  let children : Nat → List Nat := fun n => if n = 0 then [] else [n / 2]
  let assemble : Nat → List (List Bool) → Option (List Bool) := fun n rs =>
    some (if n = 0 then [] else decide (n % 2 = 1) :: rs.getD 0 [])
  have hz := Primrec.eq.comp Primrec.id (Primrec.const 0)
  have hd := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hb : Primrec (fun n : Nat => decide (n % 2 = 1)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 1)).decide
  have hc : Primrec children := Primrec.ite hz (Primrec.const [])
    (Primrec.list_cons.comp hd (Primrec.const []))
  have ha : Primrec₂ assemble :=
    Primrec.option_some.comp (Primrec.ite (hz.comp Primrec.fst) (Primrec.const [])
      (Primrec.list_cons.comp (hb.comp Primrec.fst)
        ((Primrec.list_getD []).comp Primrec.snd (Primrec.const 0))))
  apply Primrec.nat_omega_rec' bits Primrec.id hc ha
  · intro n t ht
    by_cases h : n = 0
    · simp [children, h] at ht
    · have hp : 0 < n := by omega
      simp only [children, if_neg h, List.mem_singleton] at ht
      subst t
      exact Nat.div_lt_self hp (by decide)
  · intro n
    rw [bits]
    by_cases h : n = 0 <;> simp [children, assemble, h]

private theorem bits_pos (p : PosNum) : (bits (p : Nat)).map bitSymbol = trPosNum p := by
  induction p with
  | one => simp [bits, trPosNum, bitSymbol]
  | bit0 p ih =>
    have hp := PosNum.to_nat_pos p
    have hn : (p : Nat) + p ≠ 0 := by omega
    have hd : ((p : Nat) + p) / 2 = (p : Nat) := by omega
    have hm : ((p : Nat) + p) % 2 = 0 := by omega
    rw [PosNum.cast_bit0, bits, dif_neg hn, hd, hm]
    simpa [bitSymbol, trPosNum] using congrArg (List.cons Γ'.bit0) ih
  | bit1 p ih =>
    have hn : (p : Nat) + p + 1 ≠ 0 := by omega
    have hd : ((p : Nat) + p + 1) / 2 = (p : Nat) := by omega
    have hm : ((p : Nat) + p + 1) % 2 = 1 := by omega
    rw [PosNum.cast_bit1, bits, dif_neg hn, hd, hm]
    simpa [bitSymbol, trPosNum] using congrArg (List.cons Γ'.bit1) ih

theorem exactNaturalBits : ExactNaturalBits := by
  intro n
  have hn : ((n : Num) : Nat) = n := Num.to_of_nat n
  rw [← hn]
  generalize (n : Num) = z
  cases z with
  | zero => simp [bits, trNat, trNum]
  | pos p => simpa [trNat, PosNum.of_to_nat, trNum] using bits_pos p

private theorem work_map (g : Γ') :
    (Function.update (fun _ : K' => none) K'.main (some g)) = slots (some g) none none none := by
  funext k
  cases k <;> simp [slots, Function.update]

theorem exactParameterLayout : ExactParameterLayout := by
  intro e xs
  have he := exactNaturalBits e
  have hx := PredictionBinarySentinelProof.exactNaturalEncoding xs
  have hr : (trList [inputNat xs, e]).reverse =
      Γ'.cons :: ((bits e).reverse.map bitSymbol ++ Γ'.cons :: Γ'.bit1 :: xs.map bitSymbol) := by
    simp [trList, hx, ← he, List.reverse_append, List.map_reverse, List.append_assoc]
  unfold PredictionCompilerFiniteExecution.sourceInput TM2to1.trInit
  change (true, (((trList [inputNat xs, e]).reverse.map
    (fun a : Γ' => (false, Function.update (fun _ : K' => none) K'.main (some a)))).headI).2) ::
    (((trList [inputNat xs, e]).reverse.map
      (fun a : Γ' => (false, Function.update (fun _ : K' => none) K'.main (some a)))).tail) = _
  rw [hr]
  simp only [List.map_cons, List.headI_cons, List.tail_cons, List.map_append, List.map_map, work_map]
  simp only [parameterWord, List.cons_append, List.append_assoc, List.nil_append]
  rfl

theorem numericWordPrimitiveRecursive : NumericWordPrimitiveRecursive := by
  have hi : Primrec PredictionFiniteAlphabet.inputSymbol := Primrec.dom_finite _
  have hm : Primrec (fun e => (bits e).reverse.map PredictionFiniteAlphabet.inputSymbol) :=
    Primrec.list_map (Primrec.list_reverse.comp bitsPrimitiveRecursive) (hi.comp Primrec.snd).to₂
  exact Primrec.list_cons.comp (Primrec.const (symbolIndex bottomSymbol))
    (Primrec.list_append.comp hm (Primrec.const [symbolIndex ordinaryCons, 2]))

theorem exactNumericWord : ExactNumericWord := by
  intro e
  have hb (b : Bool) : symbolIndex (rawSymbol b) = PredictionFiniteAlphabet.inputSymbol b := by
    cases b
    · exact PredictionBinarySentinelProof.exactBinarySlots.1
    · exact PredictionBinarySentinelProof.exactBinarySlots.2.1
  simp [parameterWord, numericWord, List.map_map, Function.comp_def, hb,
    PredictionFiniteAlphabet.inputSymbol]

end LogicLineages.ComputabilityKnowledge.PredictionBinaryParameterLayoutProof
