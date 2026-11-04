module
public import LogicLineages.OrdinalComparison.ParametricPairLeastFuelTargets
public import LogicLineages.OrdinalComparison.ParametricPairCollapseComputableSearchProof
public import Mathlib.Computability.RE
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.Proof
open ParametricPairMachineCode

/-- Every indexed worklist has a successful fuel, without a computability premise. -/
theorem successExists (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)) :
    ∃ fuel : Nat, (indexedEvaluate H p.1 p.2 fuel).isSome=true := by
  obtain ⟨fuel,hfuel,_⟩ := (ParametricPairCollapseComputable.Proof.exactSearch H p).2.2.2
  exact ⟨fuel,by simp [hfuel]⟩

/-- The no-success fallback in the definition is never reached. -/
theorem leastFuel_eq_find (H : Nat × Nat → Nat) (p : Nat × (Nat × Nat)) :
    leastFuel H p=Nat.find (successExists H p) := by
  classical
  simp only [leastFuel,dif_pos (successExists H p)]

/-- Least successful fuel returns the actual value and has no earlier successes. -/
theorem exactLeastFuel : Targets.ExactLeastFuel := by
  intro H p
  obtain ⟨fuel,hfuel,hearlier⟩ := (ParametricPairCollapseComputable.Proof.exactSearch H p).2.2.2
  have hle : leastFuel H p≤fuel := by
    rw [leastFuel_eq_find]
    exact Nat.find_min' (successExists H p) (by simp [hfuel])
  have hsuccess : (indexedEvaluate H p.1 p.2 (leastFuel H p)).isSome=true := by
    rw [leastFuel_eq_find]
    exact Nat.find_spec (successExists H p)
  have hge : fuel≤leastFuel H p := by
    by_contra h
    have hnone := hearlier (leastFuel H p) (by omega)
    simp [hnone] at hsuccess
  have heq : leastFuel H p=fuel := Nat.le_antisymm hle hge
  refine ⟨by simpa [heq] using hfuel,?_,?_⟩
  · intro k hk
    exact hearlier k (by simpa [heq] using hk)
  · intro k n hk
    rw [leastFuel_eq_find]
    exact Nat.find_min' (successExists H p) (by simp [hk])

attribute [local irreducible] Computable Partrec Nat.unpair Nat.sqrt
  ParametricPairMachineCode.indexedEvaluate leastFuel

/-- Joint computability of the budget yields total computability of least fuel. -/
theorem uniformComputable : Targets.UniformComputable := by
  intro H hH
  have he : Computable (fun p : (Nat × (Nat × Nat)) × Nat =>
      indexedEvaluate H p.1.1 p.1.2 p.2) :=
    (ParametricPairMachineCode.Proof.indexedComputable H hH).2.2
  have hs : Computable (fun p : (Nat × (Nat × Nat)) × Nat =>
      (indexedEvaluate H p.1.1 p.1.2 p.2).isSome) :=
    Primrec.option_isSome.to_comp.comp he
  have hp : ComputablePred (fun p : (Nat × (Nat × Nat)) × Nat =>
      (indexedEvaluate H p.1.1 p.1.2 p.2).isSome=true) := by
    have hd : Computable (fun p : (Nat × (Nat × Nat)) × Nat =>
        decide ((indexedEvaluate H p.1.1 p.1.2 p.2).isSome=true)) := by
      simpa using hs
    exact hd.computablePred
  exact (Computable.find hp (successExists H)).of_eq (fun p => (leastFuel_eq_find H p).symm)
end LogicLineages.OrdinalComparison.Source.ParametricPairLeastFuel.Proof
