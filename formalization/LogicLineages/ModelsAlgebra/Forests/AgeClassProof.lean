module

public import LogicLineages.ModelsAlgebra.Forests.AgeClassTargets
public import LogicLineages.ModelsAlgebra.Forests.AgeModelProof
public import LogicLineages.ModelsAlgebra.Forests.FiniteCodeProof

/-! Genuine countable relational age realization, with all finite class
hypotheses transported from actual forests and countability paid by finite codes. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.AgeClassProof

open FirstOrder AgeConstruction AgeModelProof

theorem forestModelClassNonempty : Targets.ForestModelClassNonempty := by
  rintro K ⟨F, hF⟩
  exact ⟨orderModel F.Carrier, F, hF, ⟨Language.Equiv.refl _ _⟩⟩

theorem forestModelClassIsoInvariant : Targets.ForestModelClassIsoInvariant := by
  rintro K M N ⟨e⟩
  constructor
  · rintro ⟨F, hF, ⟨i⟩⟩
    exact ⟨F, hF, ⟨e.comp i⟩⟩
  · rintro ⟨F, hF, ⟨i⟩⟩
    exact ⟨F, hF, ⟨e.symm.comp i⟩⟩

theorem forestModelClassFinitelyGenerated : Targets.ForestModelClassFinitelyGenerated := by
  rintro K M ⟨F, _, ⟨e⟩⟩
  let f : M → F.Carrier := e.symm
  letI : Finite M := Finite.of_injective f e.symm.injective
  exact Language.Structure.FG.of_finite

theorem forestModelClassHereditary : Targets.ForestModelClassHereditary := by
  rintro K hher M ⟨F, hF, ⟨i⟩⟩ N ⟨_, ⟨e⟩⟩
  obtain ⟨G, hGF, hGN⟩ := relationalFiniteForestPullback N F
    ⟨i.symm.toEmbedding.comp e⟩
  exact ⟨G, hher F G hF hGF, hGN⟩

theorem forestModelClassJointEmbedding : Targets.ForestModelClassJointEmbedding := by
  rintro K hj M ⟨F, hF, ⟨i⟩⟩ N ⟨G, hG, ⟨j⟩⟩
  obtain ⟨H, hH, hFH, hGH⟩ := hj F G hF hG
  obtain ⟨f⟩ := (orderModelEmbeddingCalibration F.Carrier H.Carrier).mp hFH
  obtain ⟨g⟩ := (orderModelEmbeddingCalibration G.Carrier H.Carrier).mp hGH
  exact ⟨orderModel H.Carrier, ⟨H, hH, ⟨Language.Equiv.refl _ _⟩⟩,
    ⟨f.comp i.symm.toEmbedding⟩, ⟨g.comp j.symm.toEmbedding⟩⟩

theorem forestModelClassEssentiallyCountable : Targets.ForestModelClassEssentiallyCountable := by
  classical
  intro K
  let codeModel (c : { c : FiniteCode.Code // FiniteCode.valid c = true }) : OrderModel :=
    orderModel (FiniteCode.toForest c.val c.property).Carrier
  let q := fun c => Quotient.mk' (codeModel c)
  apply (Set.countable_range q).mono
  rintro _ ⟨M, ⟨F, _, ⟨i⟩⟩, rfl⟩
  obtain ⟨c, _, hc, hFc⟩ := FiniteCodeProof.forestCodeEnumeration.2.2 F
  obtain ⟨j⟩ := (orderModelIsoCalibration F.Carrier
    (FiniteCode.toForest c hc).Carrier).mp hFc
  exact ⟨⟨c, hc⟩, Quotient.sound ⟨i.comp j.symm⟩⟩

theorem forestClassCountableRelationalRealization :
    Targets.ForestClassCountableRelationalRealization := by
  intro K hn hh hj
  apply Language.exists_countable_is_age_of_iff.mpr
  exact ⟨forestModelClassNonempty K hn, forestModelClassIsoInvariant K,
    forestModelClassEssentiallyCountable K, forestModelClassFinitelyGenerated K,
    forestModelClassHereditary K hh, forestModelClassJointEmbedding K hj⟩

end LogicLineages.ModelsAlgebra.Forests.AgeClassProof
