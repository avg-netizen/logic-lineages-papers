module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionDigitProof
open Dioph PrimitiveRecursion PrimitiveRecursionTargets

theorem digitDiophantine : DigitDiophantine := by
  intro α Q C I hQ hC hI
  have hB : DiophFn (fun v => Cipher.base (Q v)) :=
    Dioph.pow_dioph (Dioph.const_dioph 2) (Dioph.mul_dioph (Dioph.const_dioph 4) hQ)
  have hE : DiophFn (fun v => 2 ^ (I v + 1)) :=
    Dioph.pow_dioph (Dioph.const_dioph 2) (Dioph.add_dioph hI (Dioph.const_dioph 1))
  exact Dioph.mod_dioph (Dioph.div_dioph hC (Dioph.pow_dioph hB hE)) hB

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.PrimitiveRecursionDigitProof
