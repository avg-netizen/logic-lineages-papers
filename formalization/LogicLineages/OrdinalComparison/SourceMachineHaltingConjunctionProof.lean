module
public import LogicLineages.OrdinalComparison.SourceMachineHaltingConjunctionArgumentsProof
public import LogicLineages.OrdinalComparison.SourceMachineControlNonperiodicityParityProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction.Proof
open SourceBlankMachineSimulation
open SourceMachineControlNonperiodicity (gamma)

private theorem argument_parity (b e t : Nat) :
    gamma b (argument b e t)%2 = if boundedH (e,argument b e t) then 1 else 0 := by
  have h := SourceMachineControlNonperiodicity.Proof.parity_exact b (argument b e t)
    (argument_bounds b e t).2.1
  rwa [argument_valuation] at h

private theorem explicit_witness (b e t : Nat) (h : boundedH (e,argument b e t) = true) :
    Conjunction b e t (argument b e t-4) (gamma b (argument b e t))
      ((gamma b (argument b e t)-1)/2) := by
  have hb := (argument_bounds b e t).1
  have hz : argument b e t-4+4 = argument b e t := by omega
  have hp := argument_parity b e t
  rw [h] at hp
  change gamma b (argument b e t)%2 = 1 at hp
  refine ⟨?_,?_,?_⟩
  · change argument b e t-4+4 = argument b e t
    exact hz
  · rw [hz]
  · omega

theorem exactFixedWitness : Targets.ExactFixedWitness := by
  intro b e t
  refine ⟨⟨?_,?_⟩,explicit_witness b e t⟩
  · rintro ⟨z,y,w,hz,hy,hw⟩
    change z+4 = argument b e t at hz
    have hp := argument_parity b e t
    rw [hz] at hy
    cases hh : boundedH (e,argument b e t) <;> simp only [hh, Bool.false_eq_true, if_false, if_true] at hp ⊢ <;> omega
  · intro h
    exact ⟨_,_,_,explicit_witness b e t h⟩

theorem exactHaltingReduction : Targets.ExactHaltingReduction := by
  intro b e
  constructor
  · rintro ⟨t,z,y,w,h⟩
    exact (SourceBlankMachineSimulation.Proof.monotoneHalting.2 e).2
      ⟨argument b e t,(exactFixedWitness b e t).1.1 ⟨z,y,w,h⟩⟩
  · intro h
    obtain ⟨t,ht⟩ := (SourceBlankMachineSimulation.Proof.monotoneHalting.2 e).1 h
    have hh := SourceBlankMachineSimulation.Proof.monotoneHalting.1 e t (argument b e t)
      (argument_bounds b e t).2.2 ht
    obtain ⟨z,y,w,hw⟩ := (exactFixedWitness b e t).1.2 hh
    exact ⟨t,z,y,w,hw⟩
end LogicLineages.OrdinalComparison.SourceMachineHaltingConjunction.Proof
