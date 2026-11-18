module
public import LogicLineages.PermittedControl.ThresholdGuardProof
public import LogicLineages.PermittedControl.FixedEntryProgramProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison
attribute [local irreducible] ordinalAddCode ordinalSubCode rawNoteEncode rawNormCode rawComparisonCode

 theorem fixed_partner_hit_mem (f : Nat → Nat) (B : Nat) (hf : SelectedWithThreshold f B)
    (lambda mu delta : NONote) (t i : Nat) (hd : Order.IsSuccLimit delta.1.repr)
    (hi : FirstEntry f (countInitial lambda.1.repr t) (mu.1.repr+delta.1.repr) i) :
    (entryNormAt f (countInitial lambda.1.repr t) i,i) ∈ fixedEntryProgram f
      (rawNoteEncode lambda.1,ordinalAddCode (rawNoteEncode mu.1) (rawNoteEncode delta.1),t) := by
  have hc : Computable f := (selected_laws f B hf).2.1.to_comp
  have hlim : Order.IsSuccLimit (mu+delta).1.repr :=
    (note_add_repr mu delta).symm ▸ Ordinal.isSuccLimit_add mu.1.repr hd
  have hi' : FirstEntry f (countInitial lambda.1.repr t) (mu+delta).1.repr i :=
    (note_add_repr mu delta).symm ▸ hi
  have hmem := ((fixedEntryProgramEffectivity f hc).2 lambda (mu+delta) t
    (entryNormAt f (countInitial lambda.1.repr t) i) i (Or.inr hlim)).mpr ⟨hi',rfl⟩
  have he := congrArg (fun k => (entryNormAt f (countInitial lambda.1.repr t) i,i) ∈
    fixedEntryProgram f (rawNoteEncode lambda.1,k,t)) (ordinal_add_note_code mu delta)
  exact Eq.mpr he hmem

end LogicLineages.PermittedControl
