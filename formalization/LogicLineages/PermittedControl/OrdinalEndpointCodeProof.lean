module
public import LogicLineages.PermittedControl.OrdinalSubtractionCodeProof
public import LogicLineages.PermittedControl.OrdinalEndpointProgramsProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem ordinalEndpointCodeLiteral : Targets.OrdinalEndpointCodeLiteral :=
  fun a b => ⟨ordinalAddCodeLiteral a b,ordinalSubCodeLiteral a b⟩

 theorem ordinalEndpointCodeSemantic : Targets.OrdinalEndpointCodeSemantic := by
  intro a b
  letI : ONote.NF a.1 := a.2
  letI : ONote.NF b.1 := b.2
  dsimp only
  rw [ordinalAddCodeLiteral,ordinalSubCodeLiteral,rawNoteDecodeEncode,rawNoteDecodeEncode,
    rawNoteDecodeEncode,rawNoteDecodeEncode]
  exact ⟨ONote.add_nf _ _,ONote.sub_nf _ _,ONote.repr_add _ _,ONote.repr_sub _ _⟩

 theorem ordinalEndpointCodeFoundation : Targets.OrdinalEndpointCodeFoundation :=
  ⟨ordinalEndpointCodeEffective,ordinalEndpointCodeLiteral,ordinalEndpointCodeSemantic⟩

end LogicLineages.PermittedControl
