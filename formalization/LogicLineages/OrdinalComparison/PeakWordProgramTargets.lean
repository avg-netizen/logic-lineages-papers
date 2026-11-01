module
public import LogicLineages.OrdinalComparison.PeakWordProgramDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.Targets

def PrincipalBlocksCodeProgram : Prop := Primrec encodedPrincipalBlocks ∧
  ∀ o : ONote, encodedPrincipalBlocks (rawNoteEncode o)=(principalExponentBlocks o).map rawNoteEncode

def PrincipalWordCodeProgram : Prop := Primrec₂ encodedPrincipalWordFromBlocks ∧
  ∀ (es : List ONote) (c : Nat), encodedPrincipalWordFromBlocks (es.map rawNoteEncode) c=
    encodePrincipalKernelWord (principalKernelWord es c)

def PrincipalPeakWordCodeProgram : Prop := Primrec encodedPrincipalPeakWord ∧
  ∀ o : ONote, encodedPrincipalPeakWord (rawNoteEncode o)=
    encodePrincipalKernelWord (principalKernelWord (principalExponentBlocks o) 0)

def FullPrincipalPeakWordCodeProgram : Prop :=
  PrincipalBlocksCodeProgram ∧ PrincipalWordCodeProgram ∧ PrincipalPeakWordCodeProgram

end LogicLineages.OrdinalComparison.Targets
