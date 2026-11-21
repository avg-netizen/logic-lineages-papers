module
public import LogicLineages.PermittedControl.LongFieldEffectiveTailTargets
import LogicLineages.PermittedControl.FieldComparisonPeelProof
import LogicLineages.PermittedControl.ThresholdTailBridgeProof
import LogicLineages.PermittedControl.ThresholdNoteCodeProof

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

theorem omegaMultipleTailCode_calibrated (c : Nat) :
    omegaMultipleTailCode c = rawNoteEncode (omegaMultiple c).1 := by
  rcases Nat.eq_zero_or_pos c with rfl | hc
  · have hz : (omegaMultiple 0).1 = ONote.zero := by
      apply ONote.repr_inj.mp
      rw [omegaMultiple_repr, Nat.cast_zero, mul_zero] <;> rfl
    rw [hz] <;> rfl
  · let one := NONote.ofNat 1
    let monomial := ONote.oadd one.1 ⟨c,hc⟩ ONote.zero
    have hmrep : monomial.repr = Ordinal.omega0 * (c : Ordinal) := by
      change Ordinal.omega0 ^ (ONote.ofNat 1).repr * (c : Ordinal) + 0 = _
      rw [ONote.repr_ofNat, Nat.cast_one, Ordinal.opow_one, add_zero]
    letI : ONote.NF monomial := ONote.NF.oadd (inferInstance : ONote.NF one.1) ⟨c,hc⟩ ONote.NFBelow.zero
    have hm : (omegaMultiple c).1 = monomial :=
      ONote.repr_inj.mp ((omegaMultiple_repr c).trans hmrep.symm)
    rw [hm, omegaMultipleTailCode, if_neg (Nat.ne_of_gt hc)] <;> rfl

theorem longFieldPeelBoundCode_calibrated (B : Nat) (lam mu : NONote) (c : Nat) :
    longFieldPeelBoundCode B (rawNoteEncode lam.1) (rawNoteEncode mu.1) c =
      longFieldPeelBound B lam mu c := by
  simp only [longFieldPeelBoundCode,longFieldPeelBound,omegaMultipleTailCode_calibrated,
    ordinal_add_note_code,normal_norm_code,peeled_repr]

theorem longFieldTailCodes_calibrated (B : Nat) (F G : ValueField) :
    longFieldDistinctBoundCode B (longFieldCode F) (longFieldCode G) = longFieldDistinctBound B F G ∧
    longFieldSameBoundCode B (longFieldCode F) (longFieldCode G) = longFieldSameBound B F G := by
  cases F <;> cases G <;>
    simp [longFieldCode,longFieldDistinctBoundCode,longFieldSameBoundCode,longFieldDistinctBound,
      longFieldSameBound,longFieldPeelBoundCode_calibrated,omegaMultipleTailCode_calibrated,
      ordinal_add_note_code,ordinal_sub_note_code,inverseTableTailCode_correct,normal_encoded_gap_tail]

end LogicLineages.PermittedControl.FieldComparison
