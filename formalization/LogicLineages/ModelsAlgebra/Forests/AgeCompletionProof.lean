module

public import LogicLineages.ModelsAlgebra.Forests.AgeCompletionTargets
public import LogicLineages.ModelsAlgebra.Forests.AgeNecessaryProof
public import LogicLineages.ModelsAlgebra.Forests.AgeClassProof
public import LogicLineages.ModelsAlgebra.Forests.AgeReconstructionProof

/-! Full actual forest age realization. Every relational, countability, and
finite-local forest obligation is supplied by the separately checked stages. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof

open FirstOrder AgeConstruction AgeModelProof AgeNecessaryProof
  AgeClassProof AgeReconstructionProof

theorem actualForestModelAgeCalibration : Targets.ActualForestModelAgeCalibration := by
  intro K A hher hAge F
  constructor
  · intro hF
    have hmem : orderModel F.Carrier ∈ Language.order.age (orderModel A.Carrier) := by
      rw [hAge]
      exact ⟨F, hF, ⟨Language.Equiv.refl _ _⟩⟩
    exact (orderModelEmbeddingCalibration F.Carrier A.Carrier).mpr hmem.2
  · intro he
    have hfinite : Finite (orderModel F.Carrier) := by
      change Finite F.Carrier
      infer_instance
    letI := hfinite
    have hmem : orderModel F.Carrier ∈ Language.order.age (orderModel A.Carrier) :=
      ⟨Language.Structure.FG.of_finite,
        (orderModelEmbeddingCalibration F.Carrier A.Carrier).mp he⟩
    rw [hAge] at hmem
    obtain ⟨G, hG, hGF⟩ := hmem
    obtain ⟨i⟩ := (orderModelIsoCalibration G.Carrier F.Carrier).mpr hGF
    exact hher G F hG ⟨i.symm.toOrderEmbedding⟩

theorem fullForestAgeRealization : Targets.FullForestAgeRealization := by
  intro K hn hh
  constructor
  · rintro ⟨A, hA⟩
    exact realizedForestAgeHasJEP K A hA
  · intro hj
    obtain ⟨M, hcount, hAge⟩ := forestClassCountableRelationalRealization K hn hh hj
    obtain ⟨A, ⟨e⟩⟩ := countableForestModelReconstruction K M hcount hAge
    exact ⟨A, actualForestModelAgeCalibration K A hh (e.age_eq_age.trans hAge)⟩

theorem unboundedForestAgeRealization : Targets.UnboundedForestAgeRealization := by
  intro K hn hh hj hu
  obtain ⟨A, hA⟩ := (fullForestAgeRealization K hn hh).mpr hj
  exact ⟨A, hA, unboundedForestAgeCountablyInfinite K A hA hu⟩

end LogicLineages.ModelsAlgebra.Forests.AgeCompletionProof
