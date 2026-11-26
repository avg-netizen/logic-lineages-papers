module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericCompositionProof
public import LogicLineages.PersistentMarking.NumberedWindowAddressProgramProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePositiveFoldNumericChecks
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open NumberedWindowAddressAlgorithm (contextView typeBit)
open NumberedWindowAddressProgramProof (contextPrim validType)
open NumberedWindowInternalSparsePositiveFoldNumericChecks (exact_ConcretePositive)
open NumberedWindowInternalSparseAddressPositiveCalibrationTargets
open NumberedWindowInternalSparseAddressPositiveNumericCompositionProof (composition)

private theorem indicator {f : Nat → Bool} (p : Primrec f) :
    Primrec (fun x => (f x).toNat) :=
  (Primrec.cond p (Primrec.const 1) (Primrec.const 0)).of_eq (fun x => by cases h : f x <;> simp [h])

theorem exact_AddressPositiveComposition : AddressPositiveComposition := composition

theorem exact_ConcreteAddressPositive : ConcreteAddressPositive := by
  intro entries s
  have hctx : Primrec (fun n => (contextView n).isSome.toNat) :=
    indicator (Primrec.option_isSome.comp contextPrim)
  have hty : Primrec (fun n => (typeBit n).toNat) := indicator validType
  obtain ⟨cv,hcv⟩ := (GorbowPRProgram.Proof.unaryCorrespondence _).mp hctx
  obtain ⟨tv,htv⟩ := (GorbowPRProgram.Proof.unaryCorrespondence _).mp hty
  obtain ⟨raw,least,hr,hl,ha,hf,hp⟩ := exact_ConcretePositive entries s
  exact ⟨cv,tv,raw,least,hcv,htv,hr,hl,ha,hf,hp,
    composition entries s cv tv raw least hcv htv hp⟩

#print axioms exact_AddressPositiveComposition
#print axioms exact_ConcreteAddressPositive
end LogicLineages.PersistentMarking.NumberedWindowInternalSparseAddressPositiveNumericChecks
