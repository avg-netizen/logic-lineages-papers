module
public import LogicLineages.PermittedControl.FixedHeadCollapseGraphTargets
import LogicLineages.PermittedControl.ClosedOrdinaryFieldGuardProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldEffectiveProof
import LogicLineages.OrdinalComparison.RawNotationCode

@[expose] public section
namespace LogicLineages.PermittedControl.FixedHeadCollapseGraph
open OrdinalComparison FieldComparison

private def terminalArgs (p : Input) : FixedEntryClosedArgs := (p.1,0,p.2)

private theorem terminalArgsPrimitive : Primrec terminalArgs :=
  Primrec.fst.pair ((Primrec.const 0).pair Primrec.snd)

private theorem zeroDecoded : rawNoteDecode 0 = (NONote.ofNat 0).1 := by
  have code : rawNoteEncode (NONote.ofNat 0).1 = 0 := by
    simp only [NONote.ofNat,ONote.ofNat,rawNoteEncode]
  rw [← code]
  exact rawNoteDecodeEncode _

private theorem zeroDomain (p : Input) :
    DecodedClosedProperEntryDomain (terminalArgs p) ↔ domain p := by
  change (ONote.NF (rawNoteDecode p.1) ∧ ONote.NF (rawNoteDecode 0) ∧
    Order.IsSuccLimit (rawNoteDecode p.1).repr ∧
    ((rawNoteDecode 0).repr = 0 ∨ Order.IsSuccLimit (rawNoteDecode 0).repr) ∧
    (rawNoteDecode 0).repr < (rawNoteDecode p.1).repr ∧
    actualOrdinalNorm (rawNoteDecode p.1).repr ≤ p.2) ↔ domain p
  rw [zeroDecoded]
  constructor
  · rintro ⟨normal,_,limit,_,_,affordable⟩
    exact ⟨normal,limit,affordable⟩
  · rintro ⟨normal,limit,affordable⟩
    have positive : 0 < (rawNoteDecode p.1).repr :=
      Ordinal.omega0_pos.trans_le (Ordinal.omega0_le_of_isSuccLimit limit)
    exact ⟨normal,(NONote.ofNat 0).2,limit,Or.inl rfl,positive,affordable⟩

theorem guardExact : GuardExact := by
  refine ⟨closedProperEntryDomainExact.1.comp terminalArgsPrimitive,?_⟩
  intro p
  exact (closedProperEntryDomainExact.2.1 (terminalArgs p)).trans (zeroDomain p)

theorem graphEffective : GraphEffective := by
  intro f hf
  let Args := Input × Option (Nat × Nat)
  let ReadArgs := Input × (Nat × Nat)
  have result := (closedOrdinaryFieldEffective f hf).1.comp terminalArgsPrimitive.to_comp
  have pair : Computable (fields f) := by
    apply (Computable.option_bind result (Computable.snd : Computable (Prod.snd : Args → _)).to₂).of_eq
    intro p
    change (closedProperEntryResult f (terminalArgs p)).bind id = fields f p
    unfold terminalArgs fields
    cases closedProperEntryResult f (p.1,0,p.2) <;> rfl
  have sum : Primrec (fun p : ReadArgs => p.2.1 + p.2.2) :=
    Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  exact ⟨pair,Computable.option_map pair sum.to_comp.to₂⟩

end LogicLineages.PermittedControl.FixedHeadCollapseGraph
