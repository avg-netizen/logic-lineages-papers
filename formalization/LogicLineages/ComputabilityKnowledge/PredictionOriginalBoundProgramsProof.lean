module
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsTargets
public import LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundsProof
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsProof
open PredictionOriginalBoundPrograms PredictionOriginalBoundProgramsTargets

theorem uniformOrdinaryBounds : UniformOrdinaryBounds := by
  intro g hg
  have hbound : Computable (fun z : Nat × Nat => PredictionOriginalBounds.levelBound g z.1 z.2) :=
    (PredictionOriginalBounds.computableBounds g hg).1
  have hnum : Computable (fun n : Nat => PredictionOriginalBounds.levelBound g n.unpair.1 n.unpair.2) :=
    Computable.comp (f := fun z : Nat × Nat => PredictionOriginalBounds.levelBound g z.1 z.2)
      (g := Nat.unpair) hbound Computable.unpair
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp (Partrec.nat_iff.mp hnum)
  refine ⟨u, Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.id, ?_⟩
  intro m n
  rw [compile, Nat.Partrec.Code.eval_curry, hu]
  change Part.some (PredictionOriginalBounds.levelBound g (Nat.pair m n).unpair.1 (Nat.pair m n).unpair.2) = _
  rw [Nat.unpair_pair]

theorem exactTotalBoundValues : ExactTotalBoundValues := by
  intro u g hs m
  have ht : PredictionCanonicalList.TotalNat (compile u m) := by
    intro n
    exact ⟨PredictionOriginalBounds.levelBound g m n, (hs m n).symm ▸ Part.mem_some _⟩
  refine ⟨ht, ?_⟩
  intro n
  have hd : (Nat.Partrec.Code.eval (compile u m) n).Dom := (ht n).choose_spec.1
  have hv : PredictionMaximum.evalValue (compile u m) n ∈ Nat.Partrec.Code.eval (compile u m) n := by
    simp only [PredictionMaximum.evalValue, dif_pos hd]
    exact ⟨hd, rfl⟩
  rw [hs m n] at hv
  exact Part.mem_some_iff.mp hv

end LogicLineages.ComputabilityKnowledge.PredictionOriginalBoundProgramsProof
