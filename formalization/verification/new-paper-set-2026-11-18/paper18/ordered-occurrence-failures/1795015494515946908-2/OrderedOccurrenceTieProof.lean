module
public import LogicLineages.StandardControlCurrent.OrderedOccurrenceOrderProof
public import LogicLineages.StandardControlCurrent.MixedRunnerBlockProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion OrderedOccurrence

theorem tie_step (p : Matrix) (i j : Nat) (hij : i ≠ j) (ν : Nat → Nat) :
    (∃ n : Nat, (Matrix.conjunction (.equal (.variable i) (.variable j)) p).eval
      (Function.update ν i n)) ↔ (p.substitute i (.variable j)).eval ν := by
  rw [WindowProof.matrix_substitution]
  simp only [Matrix.eval,Term.value,Function.update_self,Function.update_of_ne hij.symm]
  constructor
  · rintro ⟨n,he,hp⟩
    simpa only [he] using hp
  · intro hp
    exact ⟨ν j,rfl,hp⟩

theorem tieReduction : OrderedOccurrenceTargets.TieReduction := by
  intro xs p i j hn hi hj hij
  have hl := List.length_erase_add_one hi
  refine ⟨?_,List.Nodup.erase i hn,hl,by omega⟩
  intro ν
  exact MixedRunnerBlockProof.block_erase xs i _ _ hn hi (tie_step p.compile i j hij) ν
end LogicLineages.StandardControlCurrent.OrderedOccurrenceProof
