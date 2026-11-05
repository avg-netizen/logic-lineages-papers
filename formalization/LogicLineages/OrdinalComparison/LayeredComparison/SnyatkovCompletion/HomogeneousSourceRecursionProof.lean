module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
open HomogeneousSource
attribute [local irreducible] Nat.sqrt Nat.unpair

/-- Primitive recursion for an actual one-child parser. The final applications
supply the literal equations and prove their concrete child decreases. -/
private theorem parser_primitive (P : Nat → Prop) [DecidablePred P] (name child : Nat → Nat)
    (f : Nat → List Nat × Nat) (hp : PrimrecPred P) (hn : Primrec name) (hc : Primrec child)
    (hdec : ∀ n, P n → child n < n)
    (heq : ∀ n, f n = if P n then (name n :: (f (child n)).1, (f (child n)).2) else ([], n)) :
    Primrec f := by
  let step (values : List (List Nat × Nat)) : Option (List Nat × Nat) :=
    some (if P values.length then
      (name values.length :: (values.getD (child values.length) ([], 0)).1,
        (values.getD (child values.length) ([], 0)).2)
      else ([], values.length))
  have hv : Primrec (fun values : List (List Nat × Nat) => values.getD (child values.length) ([], 0)) :=
    (Primrec.list_getD ([], 0)).comp Primrec.id (hc.comp Primrec.list_length)
  have hs : Primrec step :=
    Primrec.option_some.comp (Primrec.ite (hp.comp Primrec.list_length)
      ((Primrec.list_cons.comp (hn.comp Primrec.list_length) (Primrec.fst.comp hv)).pair (Primrec.snd.comp hv))
      ((Primrec.const []).pair Primrec.list_length))
  have h : Primrec₂ (fun (_ : Unit) n => f n) := by
    apply Primrec.nat_strong_rec _ (hs.comp Primrec.snd).to₂
    intro _ n
    unfold step
    simp only [List.length_map, List.length_range]
    rw [heq n]
    by_cases hn : P n
    · have hd := hdec n hn
      simp [hn, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hd]
    · simp only [if_neg hn]
  exact h.comp (Primrec.const ()) Primrec.id

private theorem quotient_primitive : Primrec (fun n : Nat => n / 5) :=
  Primrec.nat_div.comp Primrec.id (Primrec.const 5)
private theorem mod_primitive : Primrec (fun n : Nat => n % 5) :=
  Primrec.nat_mod.comp Primrec.id (Primrec.const 5)

theorem peelExists_primitive : Primrec Code.peelExists := by
  apply parser_primitive (fun n => n % 5 = 4) (fun n => (n / 5).unpair.1) (fun n => (n / 5).unpair.2)
    Code.peelExists (Primrec.eq.comp mod_primitive (Primrec.const 4))
    (Primrec.fst.comp (Primrec.unpair.comp quotient_primitive))
    (Primrec.snd.comp (Primrec.unpair.comp quotient_primitive))
  · intro n hn
    have hp : 0 < n := by omega
    exact lt_of_le_of_lt (Nat.unpair_right_le _) (Nat.div_lt_self hp (by decide))
  · intro n
    rw [Code.peelExists]

private theorem forallName_primitive : Primrec Code.forallName :=
  Primrec.fst.comp (Primrec.unpair.comp (quotient_primitive.comp quotient_primitive))
private theorem rawChild_primitive : Primrec (fun n : Nat => (n / 5 / 5).unpair.2) :=
  Primrec.snd.comp (Primrec.unpair.comp (quotient_primitive.comp quotient_primitive))
private theorem forallChild_primitive : Primrec Code.forallChild :=
  quotient_primitive.comp rawChild_primitive
private theorem forallTest_primitive : PrimrecPred Code.forallTest :=
  (Primrec.eq.comp mod_primitive (Primrec.const 2)).and
    ((Primrec.eq.comp (mod_primitive.comp quotient_primitive) (Primrec.const 4)).and
      (Primrec.eq.comp (mod_primitive.comp rawChild_primitive) (Primrec.const 2)))

theorem peelForall_primitive : Primrec Code.peelForall := by
  apply parser_primitive Code.forallTest Code.forallName Code.forallChild Code.peelForall
    forallTest_primitive forallName_primitive forallChild_primitive
  · intro n hn
    have hp : 0 < n := by have h := hn.1; omega
    have hd : n / 5 < n := Nat.div_lt_self hp (by decide)
    have hq := Nat.div_le_self (n / 5) 5
    have hr := Nat.unpair_right_le (n / 5 / 5)
    have hc := Nat.div_le_self (n / 5 / 5).unpair.2 5
    unfold Code.forallChild
    omega
  · intro n
    rw [Code.peelForall]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HomogeneousSourceProof
