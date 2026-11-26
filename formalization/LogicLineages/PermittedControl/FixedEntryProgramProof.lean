module
public import LogicLineages.PermittedControl.FixedEntryProgramTargets
public import LogicLineages.PermittedControl.OrdinalEndpointCodeProof
public import LogicLineages.PermittedControl.EntryEffectivityProof
public import LogicLineages.PermittedControl.EntryExistenceProof
public import LogicLineages.PermittedControl.GapInputFoundationProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem finiteOrdinalCode_correct (n : Nat) : finiteOrdinalCode n=rawNoteEncode (ONote.ofNat n) := by
  cases n with
  | zero => rfl
  | succ n => simp [finiteOrdinalCode,ordinalNodeCode,ONote.ofNat,rawNoteEncode]

 theorem canonicalInitialCode_primrec : Primrec₂ canonicalInitialCode := by
  have hn : Primrec finiteOrdinalCode := Primrec.ite (Primrec.eq.comp Primrec.id (Primrec.const 0))
    (Primrec.const 0) (ordinalNodeCode_primrec (Primrec.const 0)
      (Primrec.nat_sub.comp Primrec.id (Primrec.const 1)) (Primrec.const 0))
  have hr : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  exact ordinalAddCodeEffective.comp Primrec.fst
    (hn.comp (Primrec.nat_sub.comp Primrec.snd (hr.comp Primrec.fst)))

 theorem canonicalInitialCodeCorrect : Targets.CanonicalInitialCodeCorrect := by
  refine ⟨canonicalInitialCode_primrec,?_⟩
  intro lambda t
  letI : ONote.NF lambda.1 := lambda.2
  have hn : rawNormCode (rawNoteEncode lambda.1)=actualOrdinalNorm lambda.1.repr :=
    (rawNormCodeCorrect lambda.1).trans (actualOrdinalNorm_notationCorrespondence lambda).symm
  unfold canonicalInitialCode
  rw [hn,finiteOrdinalCode_correct,ordinalAddCodeLiteral,rawNoteDecodeEncode,rawNoteDecodeEncode,rawNoteDecodeEncode]
  refine ⟨ONote.add_nf _ _,?_⟩
  rw [ONote.repr_add,ONote.repr_ofNat]
  rfl

 theorem fixedEntryProgramEffectivity : Targets.FixedEntryProgramEffectivity := by
  intro f hf
  have hcode : Primrec (fun p : Nat×Nat×Nat =>
      (canonicalInitialCode p.1 p.2.2,p.2.1)) :=
    (canonicalInitialCode_primrec.comp Primrec.fst (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.fst.comp Primrec.snd)
  refine ⟨(entryEffectivity f hf).1.comp hcode.to_comp,?_⟩
  intro lambda mu t E i hm
  have hc := canonicalInitialCodeCorrect.2 lambda t
  let A : NONote := ⟨rawNoteDecode (canonicalInitialCode (rawNoteEncode lambda.1) t),hc.1⟩
  have hA : A.1.repr=countInitial lambda.1.repr t := hc.2
  have h := (entryEffectivity f hf).2 A mu hm E i
  dsimp only [A] at h
  rw [rawNoteEncodeDecode] at h
  simpa only [fixedEntryProgram,hc.2] using h

 theorem fixedEntryProgramTail : Targets.FixedEntryProgramTail := by
  intro f B hf lambda mu t hl hm hml ht
  have hcomp : Computable f := (selected_laws f B hf).2.1.to_comp
  obtain ⟨i,hi,hN⟩ := entryExistenceOrbit f B hf lambda.1.repr mu.1.repr t
    (normalRepresentationSound lambda) hl hm hml ht
  have hmem := ((fixedEntryProgramEffectivity f hcomp).2 lambda mu t
    (entryNormAt f (countInitial lambda.1.repr t) i) i hm).mpr ⟨hi,rfl⟩
  exact ⟨Part.dom_iff_mem.mpr ⟨_,hmem⟩,i,_,hmem,hi,hN⟩

 theorem fixedEntryProgramFoundation : Targets.FixedEntryProgramFoundation :=
  ⟨canonicalInitialCodeCorrect,fixedEntryProgramEffectivity,fixedEntryProgramTail⟩

end LogicLineages.PermittedControl
