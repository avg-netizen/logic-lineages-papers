module
public import LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixProof
open Turing PredictionFiniteAlphabet PredictionNumericPrefix PredictionNumericPrefixTargets

private theorem pr_width : Primrec width := Primrec.nat_add.comp Primrec.fst (Primrec.const 3)

private theorem pr_entry :
    Primrec (fun z : (Table × Nat × List Nat) × Nat => prefixEntry z.1.1 z.1.2.1 z.1.2.2 z.2) := by
  have hq : Primrec (fun z : (Table × Nat × List Nat) × Nat => z.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hw : Primrec (fun z : (Table × Nat × List Nat) × Nat => z.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hs : Primrec (fun z : (Table × Nat × List Nat) × Nat => z.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have ht := Primrec.nat_sub.comp (Primrec.nat_add.comp hq Primrec.snd) (Primrec.const 1)
  have hodd : PrimrecPred (fun z : (Table × Nat × List Nat) × Nat => z.2 % 2 = 1) := Primrec.eq.comp (Primrec.nat_mod.comp Primrec.snd (Primrec.const 2)) (Primrec.const 1)
  have hzero : PrimrecPred (fun z : (Table × Nat × List Nat) × Nat => z.2 = 0) := Primrec.eq.comp Primrec.snd (Primrec.const 0)
  have hl : Primrec (fun z : (Table × Nat × List Nat) × Nat =>
      (z.1.2.1 + z.2 - 1, (Sum.inl false : Action))) :=
    ht.pair (Primrec.const (Sum.inl false : Action))
  have hv : Primrec (fun z : (Table × Nat × List Nat) × Nat => z.1.2.2.getI (z.2 / 2)) :=
    Primrec.list_getI.comp hw (Primrec.nat_div.comp Primrec.snd (Primrec.const 2))
  have hwrt : Primrec (fun z : (Table × Nat × List Nat) × Nat =>
      (Sum.inr (z.1.2.2.getI (z.2 / 2)) : Action)) := Primrec.sumInr.comp hv
  have hr : Primrec (fun z : (Table × Nat × List Nat) × Nat =>
      ((if z.2 = 0 then z.1.1.2.1 else z.1.2.1 + z.2 - 1),
        (Sum.inr (z.1.2.2.getI (z.2 / 2)) : Action))) :=
    (Primrec.ite hzero hs ht).pair hwrt
  exact Primrec.ite hodd hl hr

theorem effectiveNumericAssembly : EffectiveNumericAssembly := by
  let P := Table × Nat × List Nat
  have hp : Primrec (fun z : P => z.1) := Primrec.fst
  have hq : Primrec (fun z : P => z.2.1) := Primrec.fst.comp Primrec.snd
  have hw : Primrec (fun z : P => z.2.2) := Primrec.snd.comp Primrec.snd
  have ha : Primrec (fun z : P => z.1.1) := Primrec.fst.comp hp
  have hs : Primrec (fun z : P => z.1.2.1) := Primrec.fst.comp (Primrec.snd.comp hp)
  have hr : Primrec (fun z : P => z.1.2.2) := Primrec.snd.comp (Primrec.snd.comp hp)
  have hwidth := pr_width.comp hp
  have hlen := Primrec.list_length.comp hw
  have htwice := Primrec.nat_mul.comp (Primrec.const 2) hlen
  have hstart : Primrec (fun z : P => entryState z.1 z.2.1 z.2.2.length) :=
    Primrec.ite (Primrec.eq.comp hlen (Primrec.const 0)) hs
      (Primrec.nat_sub.comp (Primrec.nat_add.comp hq htwice) (Primrec.const 1))
  have hpad := Primrec.list_range.comp
    (Primrec.nat_sub.comp (Primrec.nat_mul.comp hq hwidth) (Primrec.list_length.comp hr))
  have hbody : Primrec (fun z : P => bodyRows z.1 z.2.1) :=
    Primrec.list_append.comp hr (Primrec.list_map hpad (Primrec.const none).to₂)
  have hprefix : Primrec (fun z : P => prefixRows z.1 z.2.1 z.2.2) := by
    apply Primrec.list_map (Primrec.list_range.comp (Primrec.nat_mul.comp htwice hwidth))
    exact (Primrec.option_some.comp (pr_entry.comp (Primrec.fst.pair
      (Primrec.nat_div.comp Primrec.snd (hwidth.comp Primrec.fst))))).to₂
  exact Primrec.encode.comp (ha.pair (hstart.pair (Primrec.list_append.comp hbody hprefix)))

private theorem body_length (p : Table) (q : Nat) (h : p.2.2.length ≤ q * width p) :
    (bodyRows p q).length = q * width p := by
  simp only [bodyRows, List.length_append, List.length_map, List.length_range]
  omega

private theorem cell_lt (p : Table) {s q a : Nat} (hs : s < q) :
    s * width p + a % width p < q * width p := by
  have hp : 0 < width p := by unfold width; omega
  calc
    s * width p + a % width p < s * width p + width p := Nat.add_lt_add_left (Nat.mod_lt _ hp) _
    _ = (s + 1) * width p := by simp [Nat.add_mul]
    _ ≤ q * width p := Nat.mul_le_mul_right _ (by omega)

private theorem padding_none (n i : Nat) :
    (((List.range n).map (fun _ => (none : Option (Nat × Action))))[i]?).bind id = none := by
  rw [List.getElem?_map]
  cases (List.range n)[i]? <;> rfl

private theorem body_get (p : Table) (q i : Nat) (h : p.2.2.length ≤ q * width p)
    (hi : i < q * width p) : ((bodyRows p q)[i]?).bind id = (p.2.2[i]?).bind id := by
  unfold bodyRows
  by_cases ht : i < p.2.2.length
  · rw [List.getElem?_append_left ht]
  · have hn : p.2.2.length ≤ i := by omega
    rw [List.getElem?_append_right hn, List.getElem?_eq_none hn]
    exact padding_none _ _

theorem exactBodyLookup : ExactBodyLookup := by
  intro p q word h s a hs
  have hi := cell_lt p (a := a) hs
  change (((bodyRows p q ++ prefixRows p q word)[s * width p + a % width p]?).bind id) = _
  rw [List.getElem?_append_left (by rw [body_length p q h]; exact hi)]
  exact body_get p q _ h hi

theorem exactPrefixLookup : ExactPrefixLookup := by
  intro p q word h r a hr
  have hp : 0 < width p := by unfold width; omega
  have hi : r * width p + a % width p < 2 * word.length * width p := cell_lt p hr
  have hd : (r * width p + a % width p) / width p = r := by
    rw [Nat.mul_comm r (width p), Nat.mul_add_div hp, Nat.div_eq_of_lt (Nat.mod_lt _ hp)]
    simp
  have hindex : (q + r) * width p + a % width p = q * width p + (r * width p + a % width p) := by
    simp [Nat.add_mul, Nat.add_assoc]
  change (((bodyRows p q ++ prefixRows p q word)[(q + r) * width p + a % width p]?).bind id) = _
  rw [hindex, List.getElem?_append_right (by rw [body_length p q h]; omega), body_length p q h,
    Nat.add_sub_cancel_left]
  simp only [prefixRows, List.getElem?_map, List.getElem?_range hi, Option.map_some,
    Option.bind_some, hd, id_eq]

theorem exactBodyStep : ExactBodyStep := by
  intro p q word h x hx
  cases x with
  | mk s t =>
    change ((lookup (assembled p q word) s t.head.val).map _).map _ = _
    rw [exactBodyLookup p q word h s t.head.val hx]
    rfl

end LogicLineages.ComputabilityKnowledge.PredictionNumericPrefixProof
