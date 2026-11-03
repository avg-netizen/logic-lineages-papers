module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedCollectionTargets
public import LogicLineages.OrdinalComparison.CommonHeadCollectedRowAlgebraProof
public import LogicLineages.OrdinalComparison.RawNotationCode
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection.Proof

theorem actualKeyIdentity : Targets.ActualKeyIdentity := by
  intro basis a b
  constructor
  · intro h
    have hu := congrArg Nat.unpair h
    have hp : rawNoteEncode a.head.1 = rawNoteEncode b.head.1 ∧
        input basis a = input basis b := by
      simpa only [key, Nat.unpair_pair, Prod.mk.injEq] using hu
    have hd := congrArg rawNoteDecode hp.1
    rw [rawNoteDecodeEncode, rawNoteDecodeEncode] at hd
    exact ⟨congrArg ONote.repr hd, hp.2⟩
  · rintro ⟨hh, hi⟩
    have hn : a.head.1 = b.head.1 := ONote.repr_inj.mp hh
    simp only [key, hn, hi]

/-- Every chosen representative is the actual atom from a source occurrence. -/
theorem representative_spec (basis : List Nat) (row : Row) (k : Nat) (a : Atom)
    (h : representative basis row k = some a) :
    key basis a = k ∧ ∃ q : Int, (q, a) ∈ row.atoms := by
  classical
  unfold representative at h
  obtain ⟨p, hp, hpa⟩ := Option.map_eq_some_iff.mp h
  subst a
  refine ⟨?_, p.1, List.mem_of_find?_eq_some hp⟩
  simpa only [decide_eq_true_eq] using List.find?_some hp

theorem representative_exists (basis : List Nat) (row : Row) (k : Nat)
    (hk : k ∈ keys basis row) : ∃ a, representative basis row k = some a := by
  classical
  have hm : k ∈ row.atoms.map (fun p => key basis p.2) := List.mem_dedup.mp hk
  obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hm
  cases hf : row.atoms.find? (fun p => key basis p.2 = k) with
  | none =>
    have hn := List.find?_eq_none.mp hf p hp
    simp [hpk] at hn
  | some p =>
    exact ⟨p.2, by simp only [representative, hf, Option.map_some]⟩

private noncomputable def block (basis : List Nat) (row : Row) (k : Nat) :
    Option (Int × Atom) :=
  if blockCoefficient basis row k = 0 then none
  else (representative basis row k).map (fun a => (blockCoefficient basis row k, a))

private theorem block_spec (basis : List Nat) (row : Row) (k : Nat) (p : Int × Atom)
    (h : block basis row k = some p) :
    p.1 ≠ 0 ∧ p.1 = blockCoefficient basis row k ∧ key basis p.2 = k ∧
      ∃ q : Int, (q, p.2) ∈ row.atoms := by
  classical
  unfold block at h
  by_cases hz : blockCoefficient basis row k = 0
  · simp only [if_pos hz, reduceCtorEq] at h
  · rw [if_neg hz] at h
    obtain ⟨a, ha, hpa⟩ := Option.map_eq_some_iff.mp h
    subst p
    obtain ⟨hk, hsource⟩ := representative_spec basis row k a ha
    exact ⟨hz, rfl, hk, hsource⟩

theorem collected_atom (basis : List Nat) (row : Row) (p : Int × Atom)
    (hp : p ∈ (collect basis row).atoms) :
    p.1 ≠ 0 ∧ p.1 = blockCoefficient basis row (key basis p.2) ∧
      ∃ q : Int, (q, p.2) ∈ row.atoms := by
  change p ∈ (keys basis row).filterMap (block basis row) at hp
  obtain ⟨k, _, hk⟩ := List.mem_filterMap.mp hp
  obtain ⟨hn, hc, he, hs⟩ := block_spec basis row k p hk
  exact ⟨hn, by rw [he]; exact hc, hs⟩

/-- Every nonzero block of an original key survives, with a literal representative. -/
theorem surviving_block_complete (basis : List Nat) (row : Row) (k : Nat)
    (hk : k ∈ keys basis row) (hn : blockCoefficient basis row k ≠ 0) :
    ∃ a : Atom, (blockCoefficient basis row k, a) ∈ (collect basis row).atoms ∧
      key basis a = k ∧ ∃ q : Int, (q, a) ∈ row.atoms := by
  classical
  obtain ⟨a, ha⟩ := representative_exists basis row k hk
  obtain ⟨he, hs⟩ := representative_spec basis row k a ha
  refine ⟨a, ?_, he, hs⟩
  change (blockCoefficient basis row k, a) ∈
    (keys basis row).filterMap (block basis row)
  exact List.mem_filterMap.mpr ⟨k, hk, by simp only [block, if_neg hn, ha, Option.map_some]⟩

/-- Projection forgets only the representative's syntax, not its head or full input. -/
private noncomputable def codedRow (basis : List Nat) (row : Row) :
    CommonHeadLargeRow.Row := row.atoms.map (fun a => (a.1, key basis a.2))

private theorem coded_keys (basis : List Nat) (row : Row) :
    CommonHeadCollectedRow.keys (codedRow basis row) = keys basis row := by
  simp only [CommonHeadCollectedRow.keys, codedRow, keys, List.map_map, Function.comp_def]

private theorem coded_coefficient (basis : List Nat) (row : Row) (k : Nat) :
    CommonHeadCollectedRow.coefficient (codedRow basis row) k =
      blockCoefficient basis row k := by
  simp only [CommonHeadCollectedRow.coefficient, codedRow, blockCoefficient,
    List.map_map, Function.comp_def]

private theorem projected_blocks (basis : List Nat) (row : Row) (ks : List Nat)
    (hk : ∀ k ∈ ks, k ∈ keys basis row) :
    ((ks.filterMap (block basis row)).map (fun a => (a.1, key basis a.2))) =
      ((ks.map (fun k => (blockCoefficient basis row k, k))).filter (fun a => a.1 != 0)) := by
  classical
  induction ks with
  | nil => simp
  | cons k ks ih =>
    have ht := ih (fun j hj => hk j (List.mem_cons_of_mem k hj))
    obtain ⟨a, ha⟩ := representative_exists basis row k (hk k List.mem_cons_self)
    have he := (representative_spec basis row k a ha).1
    by_cases hz : blockCoefficient basis row k = 0
    · have hb : block basis row k = none := by simp only [block, if_pos hz]
      simpa only [List.filterMap_cons, hb, List.map_cons, List.filter_cons,
        hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] using ht
    · have hb : block basis row k = some (blockCoefficient basis row k, a) := by
        simp only [block, if_neg hz, ha, Option.map_some]
      simp [hb, hz, he, ht]

private theorem coded_collect (basis : List Nat) (row : Row) :
    codedRow basis (collect basis row) = CommonHeadCollectedRow.collect (codedRow basis row) := by
  change ((keys basis row).filterMap (block basis row)).map (fun a => (a.1, key basis a.2)) = _
  rw [projected_blocks basis row _ (fun _ h => h)]
  simp only [CommonHeadCollectedRow.collect, coded_keys, coded_coefficient]

theorem literalCollectedSupport : Targets.LiteralCollectedSupport := by
  intro basis row
  have hc := CommonHeadCollectedRow.Proof.literalCollectedSupport (codedRow basis row)
  have hp := hc.1
  rw [← coded_collect basis row, codedRow, List.pairwise_map] at hp
  refine ⟨?_, collected_atom basis row, ?_, ?_⟩
  · apply hp.imp
    intro a b hab he
    exact hab ((actualKeyIdentity basis a.2 b.2).mpr he)
  · intro hf
    refine ⟨hf.1, ?_⟩
    intro p hp
    obtain ⟨q, hq⟩ := (collected_atom basis row p hp).2.2
    exact hf.2 (q, p.2) hq
  · intro hg p hp
    obtain ⟨q, hq⟩ := (collected_atom basis row p hp).2.2
    exact hg (q, p.2) hq

private theorem coded_mass (basis : List Nat) (row : Row) :
    CommonHeadLargeRow.mass (codedRow basis row) = coefficientMass row := by
  simp only [CommonHeadLargeRow.mass, codedRow, coefficientMass, List.map_map, Function.comp_def]

theorem coefficientMass_collect_le (basis : List Nat) (row : Row) :
    coefficientMass (collect basis row) ≤ coefficientMass row := by
  have h := (CommonHeadCollectedRow.Proof.literalCollectedSupport (codedRow basis row)).2.2
  rw [← coded_collect basis row, coded_mass, coded_mass] at h
  exact h

private noncomputable def keyValue (k : Nat) : Int :=
  actualHeadValue (rawNoteDecode k.unpair.1).repr k.unpair.2

private theorem keyValue_key (basis : List Nat) (a : Atom) :
    keyValue (key basis a) = (actualHeadValue a.head.1.repr (input basis a) : Int) := by
  simp only [keyValue, key, Nat.unpair_pair]
  rw [rawNoteDecodeEncode a.head.1]

private theorem coded_weighted (basis : List Nat) (row : Row) :
    CommonHeadCollectedRow.weighted keyValue (codedRow basis row) =
      (row.atoms.map (fun a => a.1 *
        (actualHeadValue a.2.head.1.repr (input basis a.2) : Int))).sum := by
  simp only [CommonHeadCollectedRow.weighted, codedRow, List.map_map, Function.comp_def,
    keyValue_key]

theorem exactCollectedValue : Targets.ExactCollectedValue := by
  intro basis row
  have hw := CommonHeadCollectedRow.Proof.exactWeightedCollection (codedRow basis row) keyValue
  rw [← coded_collect basis row, coded_weighted, coded_weighted] at hw
  have hr : remainderValue basis (collect basis row) = remainderValue basis row := rfl
  have hv : value basis (collect basis row) = value basis row := by
    unfold value
    rw [hr, hw]
  refine ⟨rfl, rfl, hv, hr, ?_⟩
  intro he
  rw [← hv]
  simp only [value, he, List.map_nil, List.sum_nil, add_zero, hr]

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedRow.Collection.Proof
