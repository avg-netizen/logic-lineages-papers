module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesForwardProof
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesUniquenessProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesProof
open Cipher CipherTargets CipherOnesTargets

theorem onesEquationsUnique : OnesEquationsUnique := by
  intro n q u u1 h
  exact CipherOnesUniquenessProof.onesEquationsAtMostOne n q u u1 (ones n q) (shiftedOnes n q)
    h (CipherOnesForwardProof.onesEquationsForward n q h.1)

theorem onesArithmeticCharacterization : OnesArithmeticCharacterization := by
  intro n q u u1
  constructor
  · rintro ⟨hq,rfl,rfl⟩
    exact CipherOnesForwardProof.onesEquationsForward n q hq
  · intro h
    exact ⟨h.1,onesEquationsUnique n q u u1 h⟩

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.CipherOnesProof
