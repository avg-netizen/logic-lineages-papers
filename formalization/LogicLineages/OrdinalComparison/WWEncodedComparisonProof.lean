module
public import LogicLineages.OrdinalComparison.WWEncodedComparisonTargets
public import LogicLineages.OrdinalComparison.WWEncodedScalarProof
public import LogicLineages.OrdinalComparison.RawComparisonProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation

private theorem upTo_primitive : Primrec (fun p : (List Nat × List Nat) × Nat =>
    positiveComparisonUpTo p.2 p.1.1 p.1.2) := by
  have hbody : Primrec (fun p : (List Nat × List Nat) × (Nat × Bool) =>
      p.2.2 && decide (rawComparisonCode (p.1.1.getD p.2.1 0) (p.1.2.getD p.2.1 0) ≤ 1)) := by
    have ha : Primrec (fun p : (List Nat × List Nat) × (Nat × Bool) => p.1.1.getD p.2.1 0) := (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    have hb : Primrec (fun p : (List Nat × List Nat) × (Nat × Bool) => p.1.2.getD p.2.1 0) := (Primrec.list_getD 0).comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
    exact Primrec.and.comp (Primrec.snd.comp Primrec.snd)
      (Primrec.nat_le.comp (rawComparisonPrimitiveRecursive.comp ha hb) (Primrec.const 1)).decide
  have hrec := Primrec.nat_rec (Primrec.const true : Primrec (fun _ : List Nat × List Nat => true)) hbody.to₂
  change Primrec₂ (fun a : List Nat × List Nat => fun n => positiveComparisonUpTo n a.1 a.2)
  apply hrec.of_eq
  intro a n
  induction n with
  | zero => rfl
  | succ n ih =>
    change (Nat.rec true _ n && _) = _
    rw [ih]
    rfl

theorem positiveComparisonPrimitiveRecursive : Targets.PositiveComparisonPrimitiveRecursive := by
  exact upTo_primitive.comp (Primrec.id.pair
    (Primrec.nat_max.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)))

private theorem upTo_correct (n : Nat) (a b : List Nat) :
    positiveComparisonUpTo n a b = true ↔
      ∀ j < n, rawComparisonCode (a.getD j 0) (b.getD j 0) ≤ 1 := by
  induction n with
  | zero => simp [positiveComparisonUpTo]
  | succ n ih =>
    rw [positiveComparisonUpTo, Bool.and_eq_true_iff, decide_eq_true_eq, ih]
    constructor
    · rintro ⟨h, hn⟩ j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact h j hj
      · exact hn
    · intro h
      exact ⟨fun j hj => h j (Nat.lt_succ_of_lt hj), h n (Nat.lt_succ_self n)⟩

private theorem normalCodes_get (a : List NONote) (j : Nat) :
    (normalCodes a).getD j 0 = rawNoteEncode (a.getD j zeroNote).1 := by
  exact List.getD_map a zeroNote (fun x => rawNoteEncode x.1)

private theorem raw_le (a b : NONote) :
    rawComparisonCode (rawNoteEncode a.1) (rawNoteEncode b.1) ≤ 1 ↔ a.1.repr ≤ b.1.repr := by
  obtain ⟨hlt, heq, hgt⟩ := rawComparisonOrdinalCorrect a b
  constructor
  · intro h
    by_contra hn
    have he := hgt.mpr (lt_of_not_ge hn)
    omega
  · intro h
    rcases lt_or_eq_of_le h with h | h
    · rw [hlt.mpr h]; decide
    · rw [heq.mpr h]

theorem positiveComparisonSourceCorrect : Targets.PositiveComparisonSourceCorrect := by
  intro a b
  rw [positiveComparison, upTo_correct]
  have hla : (normalCodes a).length = a.length := List.length_map _
  have hlb : (normalCodes b).length = b.length := List.length_map _
  rw [hla, hlb]
  constructor
  · intro h j
    by_cases hj : j < max a.length b.length
    · exact (raw_le _ _).mp (by simpa only [normalCodes_get] using h j hj)
    · have ha : a.length ≤ j := (Nat.le_max_left _ _).trans (Nat.le_of_not_gt hj)
      have hb : b.length ≤ j := (Nat.le_max_right _ _).trans (Nat.le_of_not_gt hj)
      simp only [positiveNoteAt, List.getD_eq_default _ _ ha, List.getD_eq_default _ _ hb, le_refl]
  · intro h j hj
    simpa only [normalCodes_get] using (raw_le (a.getD j zeroNote) (b.getD j zeroNote)).mpr (h j)

private theorem queryLeftPrimitive : Primrec (fun p : EncodedQuery × List Nat => p.1.2.1.1) :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
private theorem queryRightPrimitive : Primrec (fun p : EncodedQuery × List Nat => p.1.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
private theorem queryLeftPositivePrimitive : Primrec (fun p : EncodedQuery × List Nat => p.1.2.1.2) :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst))
private theorem queryRightPositivePrimitive : Primrec (fun p : EncodedQuery × List Nat => p.1.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
private theorem queryStrictPrimitive : Primrec (fun p : EncodedQuery × List Nat => p.1.1) :=
  Primrec.fst.comp Primrec.fst

private theorem queryScalarLeftComputable : Computable (fun p : EncodedQuery × List Nat =>
    encodedScalarValue p.1.2.1.1 p.2) := by
  have heval : Computable (fun p : Nat × List Nat => encodedScalarValue p.1 p.2) := encodedScalarComputable
  apply (heval.comp (queryLeftPrimitive.to_comp.pair Computable.snd)).of_eq
  intro p
  rfl
private theorem queryScalarRightComputable : Computable (fun p : EncodedQuery × List Nat =>
    encodedScalarValue p.1.2.2.1 p.2) := by
  have heval : Computable (fun p : Nat × List Nat => encodedScalarValue p.1 p.2) := encodedScalarComputable
  apply (heval.comp (queryRightPrimitive.to_comp.pair Computable.snd)).of_eq
  intro p
  rfl
private theorem queryPositiveComputable : Computable (fun p : EncodedQuery × List Nat =>
    positiveComparison p.1.2.1.2 p.1.2.2.2) := by
  have hpos : Computable₂ positiveComparison := positiveComparisonPrimitiveRecursive.to_comp
  exact hpos.comp queryLeftPositivePrimitive.to_comp queryRightPositivePrimitive.to_comp

theorem encodedQueryAtComputable : Targets.EncodedQueryAtComputable := by
  have hlt : Computable (fun p : Nat × Nat => decide (p.1 < p.2)) := Primrec.nat_lt.decide.to_comp
  have hle : Computable (fun p : Nat × Nat => decide (p.1 ≤ p.2)) := Primrec.nat_le.decide.to_comp
  have hbody : Computable (fun p : EncodedQuery × List Nat =>
      positiveComparison p.1.2.1.2 p.1.2.2.2 &&
        cond p.1.1 (decide (encodedScalarValue p.1.2.1.1 p.2 < encodedScalarValue p.1.2.2.1 p.2))
          (decide (encodedScalarValue p.1.2.1.1 p.2 ≤ encodedScalarValue p.1.2.2.1 p.2))) :=
    Primrec.and.to_comp.comp queryPositiveComputable
      (Computable.cond queryStrictPrimitive.to_comp
        (hlt.comp (queryScalarLeftComputable.pair queryScalarRightComputable))
        (hle.comp (queryScalarLeftComputable.pair queryScalarRightComputable)))
  apply hbody.of_eq
  intro p
  cases h : p.1.1 <;> simp only [encodedQueryAt, h, Bool.cond_false, Bool.cond_true, Bool.false_eq_true, if_false, if_true]

theorem encodedQueryAtSourceCorrect : Targets.EncodedQueryAtSourceCorrect := by
  intro ι index strict a b ap bp xs
  simp only [encodedQueryAt, Bool.and_eq_true_iff]
  rw [positiveComparisonSourceCorrect ap bp, encodedScalarSourceCorrect ι index a xs,
    encodedScalarSourceCorrect ι index b xs]
  cases strict <;> simp
end LogicLineages.OrdinalComparison.Source.ForwardTranslation
