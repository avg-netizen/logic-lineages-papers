module

public import LogicLineages.ModelsAlgebra.Forests.WidthPositiveTargets
public import LogicLineages.ModelsAlgebra.Forests.SmallLeafLabelProof
public import LogicLineages.ModelsAlgebra.Forests.ThickeningProof
public import LogicLineages.ModelsAlgebra.Forests.RankEmbeddingProof
public import LogicLineages.ModelsAlgebra.Forests.WidthNegativeProof

/-! Actual common hosts for all widths at most three, including zero. Shared
finite comb templates are thickened far enough for both rank embeddings. All
calibrations are constructed; no missing supplier is a final hypothesis. -/
@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof

theorem smallWidthTemplateCalibration : Targets.SmallWidthTemplateCalibration := by
  classical
  intro m hm hm3
  obtain ⟨T, nodes, leaves, hnodes, _, _, _⟩ :=
    LaminarForestProof.binaryFamilyForestRepresentation (Fin m) (combFamily m)
      (CombForestProof.combFamilyBinary m hm)
  refine ⟨T, ?_, ?_⟩
  · have hcard := Fintype.card_congr leaves
    simpa only [Fintype.card_fin, Fintype.card_subtype, leafFinset] using hcard.symm
  · intro F hw
    obtain ⟨e, he⟩ := SmallLeafLabelProof.smallForestLeafLabeling F m hm3 hw
    let q : F.Carrier → T.Carrier := fun x => nodes ⟨(finiteLeafCluster F x).map e, he x⟩
    refine ⟨q, ?_, ?_⟩
    · intro x y
      change nodes ⟨_, he x⟩ ≤ nodes ⟨_, he y⟩ ↔ _
      rw [hnodes]
      exact Finset.map_subset_map
    · intro x y
      constructor
      · intro h
        have hh := congrArg Subtype.val (nodes.injective h)
        exact Finset.map_injective e hh
      · intro h
        exact congrArg nodes (Subtype.ext (congrArg (fun A => A.map e) h))

theorem widthZeroHasJEP : Targets.WidthZeroHasJEP := by
  classical
  intro F G hF hG
  have hempty (x : G.Carrier) : False := by
    have h := hG {x} (by simpa only [Finset.coe_singleton] using
      (IsAntichain.singleton : IsAntichain (· ≤ ·) ({x} : Set G.Carrier)))
    simp only [Finset.card_singleton] at h
    omega
  let e : G.Carrier ↪o F.Carrier := {
    toFun := fun x => False.elim (hempty x)
    inj' := fun x _ _ => False.elim (hempty x)
    map_rel_iff' := fun {x y} => False.elim (hempty x) }
  exact ⟨F, hF, ⟨(OrderIso.refl F.Carrier).toOrderEmbedding⟩, ⟨e⟩⟩

theorem widthAtMostThreeHasJEP : Targets.WidthAtMostThreeHasJEP := by
  intro m hm
  by_cases hz : m = 0
  · subst m; exact widthZeroHasJEP
  have hpos : 0 < m := Nat.pos_of_ne_zero hz
  obtain ⟨T, hTc, hcal⟩ := smallWidthTemplateCalibration m hpos hm
  intro F G hF hG
  let n := Fintype.card F.Carrier + Fintype.card G.Carrier + 1
  obtain ⟨H, points, hpoints, hHc⟩ := ThickeningProof.actualFiniteThickening T n (by dsimp [n]; omega)
  obtain ⟨qF, hqF, heF⟩ := hcal F hF
  obtain ⟨qG, hqG, heG⟩ := hcal G hG
  have hHw : WidthAtMost H.Carrier m :=
    (widthAtMost_iff_leaf_card H.forest m).mpr (hHc.trans hTc).le
  refine ⟨H, hHw, ?_, ?_⟩
  · exact RankEmbeddingProof.clusterRankEmbedding F T H n points qF hpoints hqF heF (by dsimp [n]; omega)
  · exact RankEmbeddingProof.clusterRankEmbedding G T H n points qG hpoints hqG heG (by dsimp [n]; omega)

theorem fullWidthJEPClassification : Targets.FullWidthJEPClassification := by
  intro m _
  constructor
  · intro h
    by_contra hn
    exact WidthNegativeProof.widthAtLeastFourFailsJEP m (by omega) h
  · exact widthAtMostThreeHasJEP m

end LogicLineages.ModelsAlgebra.Forests.WidthPositiveProof
