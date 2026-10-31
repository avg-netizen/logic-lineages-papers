module
public import LogicLineages.OrdinalComparison.WWFixedShiftTargets
public import LogicLineages.OrdinalComparison.WWOriginalOmegaProductProof
public import LogicLineages.OrdinalComparison.WWOriginalPositivityProof
public import LogicLineages.OrdinalComparison.EncodedCollapseProof
public import LogicLineages.OrdinalComparison.EncodedFiniteTailProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ForwardTranslation
open OriginalDomain
open LogicLineages.ComputabilityKnowledge.WWOrdinalTermSemanticsProof

private theorem positive_of_norm {a : Ordinal} (h : 0 < actualOrdinalNorm a) : 0 < a := by
  by_contra hn
  have ha : a = 0 := le_antisymm (le_of_not_gt hn) zero_le
  have hz : actualOrdinalNorm 0 = 0 := by simpa using (finiteNorm 0).2
  rw [ha, hz] at h
  omega

private theorem two_power_below {a : Ordinal} (ha : a < epsilonZero) :
    (2 : Ordinal) ^ a < epsilonZero := by
  have hω : Ordinal.omega0 ^ a < epsilonZero :=
    (Ordinal.apply_lt_nfp (Ordinal.isNormal_opow Ordinal.one_lt_omega0)).mpr ha
  exact (Ordinal.opow_le_opow_left a
    (show (2 : Ordinal) ≤ Ordinal.omega0 from (Ordinal.natCast_lt_omega0 2).le)).trans_lt hω

theorem closedPositiveValuePositive : Targets.ClosedPositiveValuePositive := by
  intro c
  induction c with
  | one => simp [ClosedPositive.evaluate, ONote.repr_one]
  | omega => simpa [ClosedPositive.evaluate, ONote.repr] using Ordinal.omega0_pos
  | add a b iha ihb =>
    change 0 < (naturalSum a.evaluate b.evaluate).1.repr
    rw [naturalSumDenotation]
    apply positive_of_norm
    rw [actualNaturalSumNormAdditivity _ _ (normalRepresentationSound a.evaluate)
      (normalRepresentationSound b.evaluate)]
    have hp := actualPositiveOrdinalNorm _ iha (normalRepresentationSound a.evaluate)
    omega
  | emul a b iha ihb =>
    let q : NONote := NONote.opow ⟨ONote.ofNat 2, inferInstance⟩ a.evaluate
    have hq : q.1.repr = (2 : Ordinal) ^ a.evaluate.1.repr := by
      change ((ONote.ofNat 2) ^ a.evaluate.1).repr = _
      letI : ONote.NF a.evaluate.1 := a.evaluate.2
      rw [ONote.repr_opow, ONote.repr_ofNat]
      rfl
    have hqp : 0 < q.1.repr := by
      rw [hq]
      exact Ordinal.opow_pos _ (by exact_mod_cast (show (0 : Nat) < 2 by omega))
    change 0 < (naturalProduct q b.evaluate).1.repr
    rw [naturalProductDenotation]
    apply positive_of_norm
    have hlo := actualNaturalProductNormLower _ _ hqp ihb
      (normalRepresentationSound q) (normalRepresentationSound b.evaluate)
    have hqn := actualPositiveOrdinalNorm _ hqp (normalRepresentationSound q)
    have hbn := actualPositiveOrdinalNorm _ ihb (normalRepresentationSound b.evaluate)
    omega

private def headNote (c : ClosedPositive) : NONote :=
  naturalProduct ⟨.oadd 1 1 .zero, ONote.NF.oadd ONote.nf_one 1 ONote.NFBelow.zero⟩ c.evaluate

private theorem headNote_value (c : ClosedPositive) : (headNote c).1.repr = fixedHead c := by
  rw [headNote, naturalProductDenotation]
  simp [fixedHead, ONote.repr]

theorem scalarFixedHeadAdmissible : Targets.ScalarFixedHeadAdmissible := by
  intro c
  constructor
  · exact actualOmegaNaturalProductInfinite _ (closedPositiveValuePositive c)
      (normalRepresentationSound c.evaluate)
  · rw [← headNote_value c]
    exact normalRepresentationSound (headNote c)

theorem scalarFixedShiftComputable : Targets.ScalarFixedShiftComputable := by
  intro c
  let z := headNote c
  have hp : Computable (fun n : Nat => encodedCollapseValue
      (encodedFiniteTail (rawNoteEncode z.1) n)) :=
    encodedCollapseComputable.comp
      (encodedFiniteTailPrimitiveRecursive.comp (Primrec.const (rawNoteEncode z.1)) Primrec.id).to_comp
  have he : (fun n : Nat => encodedCollapseValue (encodedFiniteTail (rawNoteEncode z.1) n)) =
      (fun n : Nat => actualCollapse (fixedHead c + (n : Ordinal))) := by
    funext n
    rw [(encodedFiniteTailCorrect z n).1, encodedCollapseSourceCorrect,
      (finiteTailCorrect z n).1, headNote_value c]
  rwa [he] at hp

end LogicLineages.OrdinalComparison.Source.ForwardTranslation
