module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecSupportProof
open NumberedMultisetNumeric NumberedListCodecPrimrec

theorem calibration (bound fuel : Nat) : ∀ value, value ≤ bound →
    ((parseTable bound fuel)[value]?).getD none = numbersParse fuel value := by
  induction fuel with
  | zero =>
    intro value hv
    simp [parseTable, numbersParse, List.getElem?_replicate, show value < bound+1 by omega]
  | succ fuel ih =>
    intro value hv
    have hlt : value < bound+1 := by omega
    simp only [parseTable, List.getElem?_map, List.getElem?_range hlt, Option.map_some, Option.getD_some]
    cases value with
    | zero => rfl
    | succ value =>
      have hp := Nat.right_le_pair (Nat.unpair value).1 (Nat.unpair value).2
      rw [Nat.pair_unpair] at hp
      simp only [nextEntry, numbersParse]
      rw [ih _ (by omega)]

theorem nextPrimitive : Primrec₂ nextEntry := by
  have h : Primrec₂ (fun (previous : ParseTable) (value : Nat) =>
      ((previous[(Nat.unpair value).2]?).getD none).map ((Nat.unpair value).1::·)) := by
    change Primrec (fun p : ParseTable × Nat =>
      ((p.1[(Nat.unpair p.2).2]?).getD none).map ((Nat.unpair p.2).1::·))
    apply Primrec.option_map
    · exact Primrec.option_getD.comp
        (Primrec.list_getElem?.comp Primrec.fst (Primrec.snd.comp (Primrec.unpair.comp Primrec.snd)))
        (Primrec.const none)
    · exact Primrec.to₂ (Primrec.list_cons.comp
        (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))) Primrec.snd)
  exact (Primrec.nat_casesOn' (Primrec.const (some [])) h).of_eq (by intro a b; cases b <;> rfl)

theorem tablePrimitive : Primrec₂ parseTable := by
  have hzero : Primrec (fun bound : Nat => List.replicate (bound+1) (none : Option (List Nat))) := by
    have h := Primrec.list_map (Primrec.list_range.comp Primrec.succ)
      (Primrec₂.const (none : Option (List Nat)))
    exact h.of_eq (by intro bound; simp)
  have hstep : Primrec₂ (fun bound (state : Nat × ParseTable) =>
      (List.range (bound+1)).map (nextEntry state.2)) := by
    change Primrec (fun p : Nat × (Nat × ParseTable) =>
      (List.range (p.1+1)).map (nextEntry p.2.2))
    exact Primrec.list_map (Primrec.list_range.comp (Primrec.succ.comp Primrec.fst))
      (nextPrimitive.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd).to₂
  exact (Primrec.nat_rec hzero hstep).of_eq (by intro bound fuel; induction fuel <;> simp_all [parseTable])

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedListCodecPrimrecSupportProof
