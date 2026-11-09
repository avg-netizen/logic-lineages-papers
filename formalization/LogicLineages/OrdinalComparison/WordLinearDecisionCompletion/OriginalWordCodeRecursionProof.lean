module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof.Numeric
open LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair

/-- The cache contains the actual mapped answers for every smaller numerical
code. Only the original radix-six child codes are read. -/
def mapCache {α : Type*} (op : α → Nat → Nat) (a : α) (values : List Nat) : Nat :=
  let code := values.length
  let payload := code / 6
  if code % 6 = 0 then 0 else if code % 6 = 1 then 1
  else if code % 6 = 2 then 6 * op a payload + 2
  else if code % 6 = 3 then 6 * values.getD payload 0 + 3
  else 6 * Nat.pair (values.getD payload.unpair.1 0)
    (values.getD payload.unpair.2 0) + code % 6

theorem mapCacheComputable {α : Type*} [Primcodable α] {op : α → Nat → Nat}
    (hop : Computable₂ op) : Computable (fun p : α × List Nat => mapCache op p.1 p.2) := by
  let A := α × List Nat
  have hn : Computable (fun p : A => p.2.length) := Computable.list_length.comp Computable.snd
  have hp : Computable (fun p : A => p.2.length / 6) :=
    Primrec.nat_div.to_comp.comp hn (Computable.const 6)
  have ht : Computable (fun p : A => p.2.length % 6) :=
    Primrec.nat_mod.to_comp.comp hn (Computable.const 6)
  have htag (k : Nat) : Computable (fun p : A => decide (p.2.length % 6 = k)) :=
    Primrec.eq.decide.to_comp.comp ht (Computable.const k)
  have hleft : Computable (fun p : A => (p.2.length / 6).unpair.1) :=
    Primrec.fst.to_comp.comp (Primrec.unpair.to_comp.comp hp)
  have hright : Computable (fun p : A => (p.2.length / 6).unpair.2) :=
    Primrec.snd.to_comp.comp (Primrec.unpair.to_comp.comp hp)
  have h0 : Computable (fun p : A => p.2.getD (p.2.length / 6) 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd hp
  have hl : Computable (fun p : A => p.2.getD (p.2.length / 6).unpair.1 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd hleft
  have hr : Computable (fun p : A => p.2.getD (p.2.length / 6).unpair.2 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd hright
  have hatom : Computable (fun p : A => 6 * op p.1 (p.2.length / 6) + 2) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 6) (hop.comp Computable.fst hp))
      (Computable.const 2)
  have hneg : Computable (fun p : A => 6 * p.2.getD (p.2.length / 6) 0 + 3) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 6) h0) (Computable.const 3)
  have hbin : Computable (fun p : A =>
      6 * Nat.pair (p.2.getD (p.2.length / 6).unpair.1 0)
        (p.2.getD (p.2.length / 6).unpair.2 0) + p.2.length % 6) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 6) (Primrec₂.natPair.to_comp.comp hl hr)) ht
  exact (computableIf (htag 0) (Computable.const 0)
    (computableIf (htag 1) (Computable.const 1)
      (computableIf (htag 2) hatom (computableIf (htag 3) hneg hbin)))).of_eq (fun _ => rfl)

theorem mapAtomsComputable {α : Type*} [Primcodable α] {op : α → Nat → Nat}
    (hop : Computable₂ op) : Computable₂ (fun a code => LinearRows.Code.mapAtoms (op a) code) := by
  have hg : Computable₂ (fun a values => some (mapCache op a values)) :=
    Computable.option_some.comp (mapCacheComputable hop)
  apply Computable.nat_strong_rec _ hg
  intro a code
  apply congrArg some
  have lookup (i : Nat) (hi : i < code) :
      ((List.range code).map (LinearRows.Code.mapAtoms (op a))).getD i 0 =
        LinearRows.Code.mapAtoms (op a) i := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hi]
  unfold mapCache
  simp only [List.length_map, List.length_range]
  rw [LinearRows.Code.mapAtoms]
  split_ifs <;> first | rfl | skip
  all_goals
    have hpos : 0 < code := by omega
    have hd : code / 6 < code := Nat.div_lt_self hpos (by decide)
    have hl : (code / 6).unpair.1 < code := (Nat.unpair_left_le _).trans_lt hd
    have hr : (code / 6).unpair.2 < code := (Nat.unpair_right_le _).trans_lt hd
    simp only [lookup (code / 6) hd, lookup (code / 6).unpair.1 hl,
      lookup (code / 6).unpair.2 hr]

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.OriginalWordEvaluation.Proof.Numeric
