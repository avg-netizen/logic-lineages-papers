module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingProof
public meta import LogicLineages.Audit

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingStatementChecks
open MaskingTargets

theorem fixedBitMaskParity : BitMaskParity := MaskingProof.bitMaskParity
theorem fixedBitMaskDiophantine : BitMaskDiophantine := MaskingProof.bitMaskDiophantine
theorem fixedBitAndCharacterization : BitAndCharacterization := MaskingProof.bitAndCharacterization
theorem fixedBitAndDiophantine : BitAndDiophantine := MaskingProof.bitAndDiophantine

#print axioms fixedBitMaskParity
#print axioms fixedBitMaskDiophantine
#print axioms fixedBitAndCharacterization
#print axioms fixedBitAndDiophantine
end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingStatementChecks

#audit_namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MaskingStatementChecks
