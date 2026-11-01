module
public import LogicLineages.OrdinalComparison.PositiveSourceDomainTargets
public import LogicLineages.OrdinalComparison.OrdinalSuccessorProgramProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.PositiveSourceDomain

theorem head_domain_primitive : Primrec encodedPositiveHeadDomain := by
  have hN : Primrec rawNormalCode := Primrec.nat_iff.mpr rawNormalPrimitiveRecursive
  have hp := (Primrec.eq.comp hN (Primrec.const 1)).and
    (((Primrec.eq.comp Primrec.id (Primrec.const 0)).not).and
      (Primrec.eq.comp OrdinalSuccessorProgram.primitive.1 (Primrec.const 0)))
  exact Primrec.ite hp (Primrec.const 1) (Primrec.const 0)

theorem head_domain_guard (n : Nat) : encodedPositiveHeadDomain n=1 ↔
    rawNormalCode n=1 ∧ n≠0 ∧ encodedOrdinalFiniteRemainder n=0 := by
  unfold encodedPositiveHeadDomain
  split_ifs <;> simp_all

private theorem note_code_zero (rho : NONote) : rawNoteEncode rho.1=0 ↔ rho.1.repr=0 := by
  constructor
  · intro h
    have hh := congrArg rawNoteDecode h
    rw [rawNoteDecodeEncode rho.1] at hh
    have hz : rho.1=ONote.zero := by simpa only [rawNoteDecode] using hh
    rw [hz]
    rfl
  · intro h
    letI := rho.2
    letI : ONote.NF ONote.zero := ONote.NF.zero
    have hz : rho.1=ONote.zero := ONote.repr_inj.mp (by simpa only [ONote.repr] using h)
    rw [hz]
    rfl

theorem head_domain : Targets.ActualPositiveHeadCodeDomain := by
  refine ⟨head_domain_primitive,?_⟩
  intro rho
  constructor
  · intro h
    have hg := (head_domain_guard _).mp h
    have hl := (OrdinalSuccessorProgram.classification rho).mp hg.2.2
    rcases hl with hz | hl
    · exact (hg.2.1 ((note_code_zero rho).mpr hz)).elim
    · exact ⟨hl,normalRepresentationSound rho⟩
  · rintro ⟨hl,_⟩
    apply (head_domain_guard _).mpr
    refine ⟨(rawNormalCorrect rho.1).mpr rho.2,?_,
      (OrdinalSuccessorProgram.classification rho).mpr (Or.inr hl)⟩
    intro hz
    have hrepr := (note_code_zero rho).mp hz
    have hp := hl.bot_lt
    rw [hrepr] at hp
    exact lt_irrefl _ hp

end LogicLineages.OrdinalComparison.PositiveSourceDomain
