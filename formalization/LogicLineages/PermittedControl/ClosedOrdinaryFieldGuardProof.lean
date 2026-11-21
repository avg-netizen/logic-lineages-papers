module
public import LogicLineages.PermittedControl.ClosedOrdinaryFieldTargets
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.OrdinalComparison.RawComparisonProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.ActualOrdinalNorm
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.FieldComparison
open OrdinalComparison

private theorem proper_guard_primitive : Primrec closedProperEntryGuard := by
  have hl : Primrec (fun p : FixedEntryClosedArgs => p.1) := Primrec.fst
  have hm : Primrec (fun p : FixedEntryClosedArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : FixedEntryClosedArgs => p.2.2) := Primrec.snd.comp Primrec.snd
  have hg1 := terminalEntryScanGuardExact.1.comp (hl.pair hm)
  have hg2 := terminalEntryScanGuardExact.1.comp (hm.pair hl)
  have ho : PrimrecPred (fun p : FixedEntryClosedArgs => rawComparisonCode p.2.1 p.1 = 0) :=
    Primrec.eq.comp (rawComparisonPrimitiveRecursive.comp hm hl) (Primrec.const 0)
  have hn : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have ha : PrimrecPred (fun p : FixedEntryClosedArgs => rawNormCode p.1 ≤ p.2.2) :=
    Primrec.nat_le.comp (hn.comp hl) ht
  exact Primrec.and.comp (Primrec.and.comp hg1 hg2) (ho.and ha).decide

private theorem code_order_norm (p : FixedEntryClosedArgs)
    (hl : ONote.NF (rawNoteDecode p.1)) (hm : ONote.NF (rawNoteDecode p.2.1)) :
    (rawComparisonCode p.2.1 p.1 = 0 ↔ (rawNoteDecode p.2.1).repr < (rawNoteDecode p.1).repr) ∧
    rawNormCode p.1 = actualOrdinalNorm (rawNoteDecode p.1).repr := by
  let l : NONote := ⟨rawNoteDecode p.1,hl⟩
  let m : NONote := ⟨rawNoteDecode p.2.1,hm⟩
  have hle : rawNoteEncode l.1 = p.1 := rawNoteEncodeDecode p.1
  have hme : rawNoteEncode m.1 = p.2.1 := rawNoteEncodeDecode p.2.1
  have hord := (rawComparisonOrdinalCorrect m l).1
  rw [hle,hme] at hord
  have hnorm := (rawNormCodeCorrect l.1).trans (actualOrdinalNorm_notationCorrespondence l).symm
  rw [hle] at hnorm
  exact ⟨hord,hnorm⟩

private theorem proper_guard_raw (p : FixedEntryClosedArgs) :
    closedProperEntryGuard p = true ↔ DecodedClosedProperEntryDomain p := by
  simp only [closedProperEntryGuard,Bool.and_eq_true,decide_eq_true_eq,DecodedClosedProperEntryDomain]
  constructor
  · rintro ⟨⟨hf,hr⟩,ho,ha⟩
    obtain ⟨hln,hmn,hmu⟩ := (terminalEntryScanGuardExact.2 (p.1,p.2.1)).mp hf
    have hlam := ((terminalEntryScanGuardExact.2 (p.2.1,p.1)).mp hr).2.2
    obtain ⟨hord,hnorm⟩ := code_order_norm p hln hmn
    have hlt := hord.mp ho
    have hlam' : Order.IsSuccLimit (rawNoteDecode p.1).repr := by
      refine hlam.resolve_left ?_
      intro hz
      rw [hz] at hlt
      exact (not_lt_of_ge (show 0 ≤ (rawNoteDecode p.2.1).repr from zero_le)) hlt
    exact ⟨hln,hmn,hlam',hmu,hlt,by rwa [hnorm] at ha⟩
  · rintro ⟨hln,hmn,hlam,hmu,hord,ha⟩
    have hf := (terminalEntryScanGuardExact.2 (p.1,p.2.1)).mpr ⟨hln,hmn,hmu⟩
    have hr := (terminalEntryScanGuardExact.2 (p.2.1,p.1)).mpr ⟨hmn,hln,Or.inr hlam⟩
    obtain ⟨ho,hnorm⟩ := code_order_norm p hln hmn
    exact ⟨⟨hf,hr⟩,ho.mpr hord,by rwa [hnorm]⟩

theorem closedProperEntryDomainExact : ClosedProperEntryDomainExact := by
  refine ⟨proper_guard_primitive,proper_guard_raw,?_⟩
  intro lam mu x
  rw [proper_guard_raw]
  have hl : rawNoteDecode (rawNoteEncode lam.1) = lam.1 := rawNoteDecodeEncode lam.1
  have hm : rawNoteDecode (rawNoteEncode mu.1) = mu.1 := rawNoteDecodeEncode mu.1
  simp only [DecodedClosedProperEntryDomain,hl,hm,ClosedOrdinaryValueDomain,ProperField]
  constructor
  · rintro ⟨_,_,hlam,hmu,hord,ha⟩
    exact ⟨⟨hlam,hmu,hord⟩,ha⟩
  · rintro ⟨⟨hlam,hmu,hord⟩,ha⟩
    exact ⟨lam.2,mu.2,hlam,hmu,hord,ha⟩

end LogicLineages.PermittedControl.FieldComparison
