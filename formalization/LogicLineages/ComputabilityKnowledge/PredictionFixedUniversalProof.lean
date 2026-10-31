module
public import LogicLineages.ComputabilityKnowledge.PredictionFixedUniversalTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFixedUniversal

theorem universalPartialRecursive : Targets.UniversalPartialRecursive := by
  have hc : Computable (fun p : Nat × Nat => Nat.Partrec.Code.ofNatCode p.2) :=
    (Computable.ofNat Nat.Partrec.Code).comp Computable.snd
  have hi : Computable (fun p : Nat × Nat => PredictionSentinelDecode.ordinaryInputCode p.1) :=
    PredictionSentinelDecode.ordinaryInputPrimitiveRecursive.to_comp.comp Computable.fst
  exact (Nat.Partrec.Code.eval_part.comp hc hi).to₂

/-- The witness is existential, obtained once for the two-input universal partial
function. No per-index code selection or chosen program definition is introduced. -/
theorem fixedVectorUniversal : Targets.FixedVectorUniversal := by
  have hf : Nat.Partrec' vectorRun := Nat.Partrec'.part_iff₂.mpr universalPartialRecursive
  exact Turing.ToPartrec.Code.exists_code hf

theorem fixedUniversal : Targets.FixedUniversal := by
  obtain ⟨U, hU⟩ := fixedVectorUniversal
  refine ⟨U, ?_⟩
  intro e xs
  have h := hU ⟨[PredictionBinarySentinel.inputNat xs, e], rfl⟩
  change U.eval [PredictionBinarySentinel.inputNat xs, e] =
    (fun n : Nat => [n]) <$> (Nat.Partrec.Code.ofNatCode e).eval
      (PredictionSentinelDecode.ordinaryInputCode (PredictionBinarySentinel.inputNat xs)) at h
  rw [PredictionSentinelDecode.ordinaryInputCorrect xs] at h
  exact h
end LogicLineages.ComputabilityKnowledge.PredictionFixedUniversal
