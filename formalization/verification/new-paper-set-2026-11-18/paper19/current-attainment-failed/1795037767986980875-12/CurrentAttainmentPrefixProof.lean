module
public import LogicLineages.ControlSensitivityCurrent.CurrentAttainmentDataProof
public import LogicLineages.OrdinalComparison.ControlComputability
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentAttainment

open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.PermittedControl

private theorem terminal_agrees (a : Ordinal) (ha : a < epsilonZero) :
    (terminalWith Phi a).2 = actualReplacementCount a := by
  have hnew := terminal_firstFinite Phi a ha
  have hold := actualTerminalFirstFinite a ha
  change (actualDescentStep^[ (terminalWith Phi a).2 ]) a = _ ∧
    (∀ i, i < (terminalWith Phi a).2 → Ordinal.omega0 ≤ (actualDescentStep^[i]) a) at hnew
  apply le_antisymm
  · by_contra! h
    have he := hnew.2 _ h
    rw [hold.1] at he
    exact (not_lt_of_ge he) (Ordinal.natCast_lt_omega0 _)
  · by_contra! h
    have he := hold.2 _ h
    rw [hnew.1] at he
    exact (not_lt_of_ge he) (Ordinal.natCast_lt_omega0 _)

theorem count_correct (l : NONote) (hl : Order.IsSuccLimit l.1.repr) (t : Nat)
    (ht : actualOrdinalNorm l.1.repr ≤ t) :
    count (rawNoteEncode l.1) t = actualHeadCount l.1.repr t := by
  let b := ⟨ONote.ofNat (t - actualOrdinalNorm l.1.repr), ONote.nf_ofNat _⟩
  obtain ⟨hNF, hval, _⟩ := encodedNaturalSumSourceCorrect l b
  let a : NONote := ⟨_, hNF⟩
  have e : encodedNaturalSum (rawNoteEncode l.1) (rawNoteEncode b.1) = rawNoteEncode a.1 :=
    (rawNoteEncodeDecode _).symm
  have ea : a.1.repr = actualHeadInitial l.1.repr t := by
    change _ = l.1.repr + ((t - actualOrdinalNorm l.1.repr : Nat) : Ordinal)
    exact hval.trans (by
      change ordinalNaturalSum _ ((ONote.ofNat _).repr) = _
      rw [ONote.repr_ofNat, actualNaturalSumFiniteRight])
  have hnormal : rawNormalCode (rawNoteEncode a.1) = 1 := (rawNormalCorrect a.1).mpr a.2
  have hmem := (firstFinite_correct Phi a).1
  have hc := terminal_agrees a.1.repr (normalRepresentationSound a)
  unfold count
  dsimp only
  rw [encoded_norm, encodedNatNoteCorrect, e, if_pos hnormal]
  rw [Part.getOrElse_of_dom _ hmem.1, Part.get_eq_of_mem hmem hmem.1, hc, ea]
  rfl

theorem completePrefix : CurrentAttainmentTargets.CompletePrefix := by
  intro l hl q b
  unfold finitePrefix
  rw [List.any_eq_true]
  constructor
  · rintro ⟨t, hm, ht⟩
    have h := of_decide_eq_true ht
    rw [encoded_norm] at h
    refine ⟨t, List.mem_range.mp hm, h.1, h.2.1, ?_⟩
    rw [← count_correct l hl t h.1]
    exact h.2.2
  · rintro ⟨t, hm, ht, ha, hr⟩
    refine ⟨t, List.mem_range.mpr hm, decide_eq_true ?_⟩
    rw [encoded_norm, count_correct l hl t ht]
    exact ⟨ht, ha, hr⟩

theorem count_computable : Computable₂ count := by
  let search := fun n : Nat => if rawNormalCode n = 1 then terminalSearchWith Phi n else Part.some 0
  have hnorm : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hguard : PrimrecPred (fun n : Nat => rawNormalCode n = 1) :=
    Primrec.eq.comp hnorm (Primrec.const 1)
  have hstep := encodedFiniteAlgorithmsPrimitiveRecursive.1.to_comp.comp (encodedStates_computable Phi Phi_computable)
  have hpart : Partrec (terminalSearchWith Phi) := Partrec.rfind hstep.partrec.to₂
  have hsearch : Partrec search := by
    apply (Partrec.cond hguard.decide.to_comp hpart Partrec.const').of_eq
    intro n
    simp [search]
  have hinput : Primrec (fun p : Nat × Nat =>
      encodedNaturalSum p.1 (encodedNatNote (p.2 - rawNormCode p.1))) :=
    encodedNaturalSumPrimitiveRecursive.comp Primrec.fst
      (encodedKernelBuildersPrimitiveRecursive.1.comp (Primrec.nat_sub.comp Primrec.snd
        ((Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp Primrec.fst)))
  apply (hsearch.comp hinput.to_comp).of_eq_tot
  intro p
  let n := encodedNaturalSum p.1 (encodedNatNote (p.2 - rawNormCode p.1))
  change count p.1 p.2 ∈ search n
  by_cases h : rawNormalCode n = 1
  · let a : NONote := ⟨rawNoteDecode n, (rawNormalDecodeCorrect n).mp h⟩
    have hm := (firstFinite_correct Phi a).1
    rw [rawNoteEncodeDecode] at hm
    unfold search count
    change (if rawNormalCode n = 1 then (terminalSearchWith Phi n).getOrElse 0 else 0)
      ∈ (if rawNormalCode n = 1 then terminalSearchWith Phi n else Part.some 0)
    rw [if_pos h, if_pos h, Part.getOrElse_of_dom _ hm.1]
    exact Part.get_mem _
  · simpa [search, count, n, h]

end LogicLineages.ControlSensitivityCurrent.CurrentAttainment
