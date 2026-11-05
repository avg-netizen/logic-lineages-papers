module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationTargets

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationSemanticProof
open MinimizationTargets

private theorem zeroTestTrue (p : Part Nat) :
    true ∈ p.map (fun z => decide (z = 0)) ↔ 0 ∈ p := by
  simp [Part.mem_map_iff]

private theorem zeroTestFalse (p : Part Nat) :
    false ∈ p.map (fun z => decide (z = 0)) ↔ ∃ z : Nat, z ∈ p ∧ z ≠ 0 := by
  simp [Part.mem_map_iff]

theorem ordinaryRfindSpecification : OrdinaryRfindSpecification := by
  intro c a start y
  rw [Nat.Partrec.Code.eval,Nat.unpaired,Nat.unpair_pair]
  change y ∈ (Nat.rfind (fun i =>
    (Nat.Partrec.Code.eval c (Nat.pair a (i + start))).map (fun z => decide (z = 0)))).map
      (fun t => t + start) ↔ _
  rw [Part.mem_map_iff]
  constructor
  · rintro ⟨t,ht,hy⟩
    obtain ⟨hz,he⟩ := Nat.mem_rfind.mp ht
    exact ⟨t,hy.symm,(zeroTestTrue _).1 hz,fun i hi => (zeroTestFalse _).1 (he hi)⟩
  · rintro ⟨t,hy,hz,he⟩
    refine ⟨t,Nat.mem_rfind.mpr ⟨(zeroTestTrue _).2 hz,?_⟩,hy.symm⟩
    intro i hi
    exact (zeroTestFalse _).2 (he i hi)

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.MinimizationSemanticProof
