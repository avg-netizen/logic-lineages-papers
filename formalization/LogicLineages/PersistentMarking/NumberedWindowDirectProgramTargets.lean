module

public import LogicLineages.PersistentMarking.NumberedWindowDirectAlgorithm
public import LogicLineages.ComputabilityKnowledge.GorbowPRProgramDefinitions
public import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets
open LogicLineages.ComputabilityKnowledge List.Vector NumberedWindowDirectAlgorithm

def OccurrenceCertificateParsing : Prop :=
  Primrec readEntry ∧ Primrec readWitness

def MultisetDomainProgram : Prop := ∀ (scalar : Nat → Bool), Primrec scalar →
  ∃ p : GorbowPRProgram.Program 1, ∀ n,
    GorbowPRProgram.evaluate p (n ::ᵥ List.Vector.nil) = (typedList scalar n).toNat

def DirectCertificateProgram : Prop := ∀ (scalar : Nat → Bool) (positive : Nat → Nat → Nat → Bool),
  Primrec scalar → Primrec (fun v : Nat × Nat × Nat => positive v.1 v.2.1 v.2.2) →
  ∃ p : GorbowPRProgram.Program 3, ∀ src cert dst,
    GorbowPRProgram.evaluate p (src ::ᵥ cert ::ᵥ dst ::ᵥ List.Vector.nil) =
      (direct scalar positive src cert dst).toNat

end LogicLineages.PersistentMarking.NumberedWindowDirectProgramTargets
