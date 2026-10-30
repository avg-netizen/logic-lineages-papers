module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionLinearTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionEmbedding
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.LinearAlgebra.Basis.VectorSpace
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem socle_correction_linear_embedding : Targets.groupSocleCorrectionLinearEmbedding.{u} := by
  intro G _ p B S
  obtain ⟨e,he,heval⟩ := socle_correction_embedding G p B S
  exact ⟨e.toZModLinearMap p,he,heval⟩

theorem socle_correction_finite_rank : Targets.groupSocleCorrectionFiniteRank.{u} := by
  intro G _ p _ B S _
  let D := socleCorrectionDomain G p B S
  let Q := SocleCorrectionQuotient G p B S
  let i : D → B := fun x => ⟨x,x.property.1.1⟩
  have hi : Function.Injective i := by
    intro x y h
    have hv := congrArg (fun z : B => (z:G)) h
    exact Subtype.ext hv
  letI : Finite D := Finite.of_injective i hi
  let N := (pStep p S).comap D.subtype
  letI : Finite Q := Finite.of_surjective (QuotientAddGroup.mk' N) (QuotientAddGroup.mk'_surjective N)
  letI : Module.Free (ZMod p) Q := Module.Free.of_divisionRing _ _
  exact ⟨inferInstance,(rank_le_card (ZMod p) Q).trans_lt (Cardinal.lt_aleph0_of_finite Q)⟩

theorem socle_correction_rank_le : Targets.groupSocleCorrectionRankLe.{u} := by
  intro G _ p _ B S
  obtain ⟨e,he,_⟩ := socle_correction_linear_embedding G p B S
  letI : Module.Free (ZMod p) (SocleCorrectionQuotient G p B S) := Module.Free.of_divisionRing _ _
  exact e.rank_le_of_injective he

end LogicLineages.ModelsAlgebra.PGroups
