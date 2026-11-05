module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityTargets
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ReductionProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityProof
open Undecidability UndecidabilityTargets

private theorem computablePredPreimage {α β : Type} [Primcodable α] [Primcodable β]
    (p : β → Prop) (hp : ComputablePred p) (f : α → β) (hf : Computable f) :
    ComputablePred (fun x => p (f x)) := by
  obtain ⟨dp,hp⟩ := hp
  exact ⟨fun x => dp (f x),hp.comp hf⟩

/-- Actual halting is RE. The complement theorem is not used. -/
theorem natHaltingRE : NatHaltingRE := by
  have hDecode : Computable Nat.Partrec.Code.ofNatCode := by
    simpa only [Nat.Partrec.Code.ofNatCode_eq] using (Computable.ofNat Nat.Partrec.Code)
  exact (Nat.Partrec.Code.eval_part.comp hDecode (Computable.const 0)).dom_re

/-- Pull a hypothetical Nat-coded decider back along the computable ordinary
code encoding, contradicting the existing proved halting theorem. -/
theorem natHaltingUndecidable : NatHaltingUndecidable := by
  intro h
  have hCodes : ComputablePred (fun c : Nat.Partrec.Code => natHaltsZero (Encodable.encode c)) :=
    computablePredPreimage natHaltsZero h Encodable.encode Computable.encode
  apply ComputablePred.halting_problem 0
  apply hCodes.of_eq
  intro c
  change (Nat.Partrec.Code.eval (Nat.Partrec.Code.ofNatCode (Encodable.encode c)) 0).Dom ↔
    (Nat.Partrec.Code.eval c 0).Dom
  rw [← Nat.Partrec.Code.ofNatCode_eq,Denumerable.ofNat_encode]

/-- The exact original polynomial-root undecidability target, using the
proved RE reduction and the actual RE halting witness, with no new premise. -/
theorem encodedPolynomialUndecidable : Targets.EncodedPolynomialUndecidable := by
  intro h
  obtain ⟨reduce,hcomp,hcorrect⟩ := ReductionProof.rePolynomialReduction natHaltsZero natHaltingRE
  have hPullback := computablePredPreimage encodedPolynomialSolvable h reduce hcomp
  exact natHaltingUndecidable (hPullback.of_eq (fun x => (hcorrect x).symm))

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.UndecidabilityProof
