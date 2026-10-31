module
public import LogicLineages.ComputabilityKnowledge.PredictionSentinelDecodeTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSentinelDecode
open PredictionBinarySentinel

theorem zeroConvention : Targets.ZeroConvention := by
  constructor <;> rw [decode] <;> simp

private theorem decode_step (n : Nat) (b : Bool) (hn : 0 < n) :
    decode (2*n+b.toNat) = decode n ++ [b] := by
  have h : ¬ 2*n+b.toNat < 2 := by omega
  have hd : (2*n+b.toNat)/2=n := by cases b <;> simp <;> omega
  have hm : decide ((2*n+b.toNat)%2=1)=b := by cases b <;> simp [Nat.add_mod, Nat.mul_mod]
  rw [decode]
  simp only [dif_neg h, hd, hm]

private theorem decode_fold (xs : List Bool) (n : Nat) (hn : 0 < n) :
    decode (xs.foldl (fun a b => 2*a+b.toNat) n) = decode n ++ xs := by
  induction xs generalizing n with
  | nil => simp
  | cons b xs ih =>
    rw [List.foldl_cons, ih _ (by omega), decode_step n b hn]
    simp [List.append_assoc]

theorem roundtrip : Targets.Roundtrip := by
  intro xs
  simpa [inputNat, zeroConvention.2] using decode_fold xs 1 (by decide)

private theorem input_append (xs : List Bool) (b : Bool) :
    inputNat (xs ++ [b]) = 2 * inputNat xs + b.toNat := by
  simp [inputNat, List.foldl_append]

theorem positiveInverse : Targets.PositiveInverse := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rw [decode]
    split
    · rename_i hn
      have hcases : n=0 ∨ n=1 := by omega
      rcases hcases with rfl | rfl <;> simp [inputNat]
    · rename_i hn
      rw [input_append, ih _ (Nat.div_lt_self (by omega) (by decide))]
      have hpos : 1 ≤ n/2 := by omega
      rw [Nat.max_eq_left hpos, Nat.max_eq_left (by omega : 1 ≤ n)]
      have hm : n%2=0 ∨ n%2=1 := by omega
      rcases hm with hm | hm <;> simp [hm] <;> omega

theorem decodePrimitiveRecursive : Targets.DecodePrimitiveRecursive := by
  let children : Nat → List Nat := fun n => if n<2 then [] else [n/2]
  let assemble : Nat → List (List Bool) → Option (List Bool) := fun n rs =>
    some (if n<2 then [] else rs.getD 0 [] ++ [decide (n%2=1)])
  have hs : PrimrecPred (fun n : Nat => n<2) := Primrec.nat_lt.comp Primrec.id (Primrec.const 2)
  have hd : Primrec (fun n : Nat => n/2) := Primrec.nat_div.comp Primrec.id (Primrec.const 2)
  have hb : Primrec (fun n : Nat => decide (n%2=1)) :=
    (Primrec.eq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2)) (Primrec.const 1)).decide
  have hc : Primrec children := Primrec.ite hs (Primrec.const [])
    (Primrec.list_cons.comp hd (Primrec.const []))
  have ha : Primrec₂ assemble := by
    have hr : Primrec (fun p : Nat × List (List Bool) => p.2.getD 0 []) :=
      (Primrec.list_getD []).comp Primrec.snd (Primrec.const 0)
    exact (Primrec.option_some.comp (Primrec.ite (hs.comp Primrec.fst) (Primrec.const [])
      (Primrec.list_append.comp hr (Primrec.list_cons.comp (hb.comp Primrec.fst) (Primrec.const []))))).to₂
  apply Primrec.nat_omega_rec' decode Primrec.id hc ha
  · intro n t ht
    by_cases hn : n<2
    · simp [children, hn] at ht
    have hd : n/2 < n := Nat.div_lt_self (by omega) (by decide)
    have ht' : t=n/2 := by simpa [children, hn] using ht
    rw [ht']; exact hd
  · intro n
    rw [decode]
    by_cases hn : n<2 <;> simp [children, assemble, hn]

theorem ordinaryInputCorrect : Targets.OrdinaryInputCorrect := by
  intro xs
  unfold ordinaryInputCode
  rw [roundtrip xs]

theorem ordinaryInputPrimitiveRecursive : Targets.OrdinaryInputPrimitiveRecursive :=
  Primrec.encode.comp decodePrimitiveRecursive
end LogicLineages.ComputabilityKnowledge.PredictionSentinelDecode
