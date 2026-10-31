module
public import LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsTargets
public import LogicLineages.ComputabilityKnowledge.PredictionSecondJumpProof
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsProof
open PredictionCanonicalTapeBounds PredictionCanonicalTapeBoundsTargets

private theorem value_mem (c : Nat.Partrec.Code) (hc : PredictionCanonicalList.TotalNat c) (n : Nat) :
    PredictionMaximum.evalValue c n ∈ Nat.Partrec.Code.eval c n := by
  have hd : (Nat.Partrec.Code.eval c n).Dom := (hc n).choose_spec.1
  simp only [PredictionMaximum.evalValue, dif_pos hd]
  exact ⟨hd,rfl⟩

theorem exactCanonicalCoverage : ExactCanonicalCoverage := by
  constructor
  · intro f hf
    obtain ⟨i,hi,_⟩ := PredictionCanonicalListProof.exhaustiveTotalComputableFunctions f hf
    refine ⟨i,?_⟩
    intro n
    have htotal := (PredictionSecondJumpProof.fullCanonicalList.2.2.1 i).2
    have hv := value_mem _ htotal n
    rw [hi n] at hv
    exact Part.mem_some_iff.mp hv
  · intro i
    have htotal := (PredictionSecondJumpProof.fullCanonicalList.2.2.1 i).2
    have hpart : Partrec (fun n => Nat.Partrec.Code.eval (PredictionCanonicalList.canonicalCode i) n) :=
      Nat.Partrec.Code.eval_part.comp (Computable.const _) Computable.id
    exact hpart.of_eq_tot (value_mem _ htotal)

theorem exactCanonicalBounds : ExactCanonicalBounds := by
  intro m n
  rw [PredictionOriginalBounds.literalFiniteMaximum]
  rfl

theorem actualSecondJumpBoundIndices : ActualSecondJumpBoundIndices := by
  obtain ⟨u,_,hu,hs⟩ := PredictionSecondJumpProof.uniformSecondJumpMaximumIndices
  have hpos : ComputableIn PredictionSecondJump.secondJumpOracles (positiveIndex u) :=
    OracleRelativeRecursionProof.relativeComposition PredictionSecondJump.secondJumpOracles
      (PredictionSecondJump.compiledBoundIndex u) Nat.succ hu Primrec.succ.computableIn
  refine ⟨u,hpos,?_⟩
  intro k
  have hk := hs (k+1) (by omega)
  refine ⟨hk.1,?_⟩
  intro n
  have hv := value_mem _ hk.1 n
  rw [hk.2 n] at hv
  rw [exactCanonicalBounds]
  exact Part.mem_some_iff.mp hv

end LogicLineages.ComputabilityKnowledge.PredictionCanonicalTapeBoundsProof
