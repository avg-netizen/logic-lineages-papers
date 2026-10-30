module
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionStrictRankTargets
public import LogicLineages.ModelsAlgebra.PGroups.SocleCorrectionLinear
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups
universe u

theorem socle_correction_strict_rank : Targets.groupSocleCorrectionStrictRank.{u} := by
  classical
  intro G _ p _ B S _
  let Q := SocleCorrectionQuotient G p B S
  let U := UlmLayer p S
  let N := (pStep p S).comap (socleCorrectionDomain G p B S).subtype
  letI modQ : Module (ZMod p) Q := inferInstance
  letI modU : Module (ZMod p) U := inferInstance
  letI freeQ : Module.Free (ZMod p) Q := Module.Free.of_divisionRing _ _
  letI freeU : Module.Free (ZMod p) U := Module.Free.of_divisionRing _ _
  letI : Finite Q := (socle_correction_finite_rank G p B S).1
  obtain ⟨e,he,heval⟩ := socle_correction_linear_embedding G p B S
  have hsurj : Function.Surjective e ↔ Function.Surjective (socleCorrectionClass G p B S) := by
    constructor
    · intro h y
      obtain ⟨z,hz⟩ := h y
      obtain ⟨x,hx⟩ := QuotientAddGroup.mk'_surjective N z
      refine ⟨x,?_⟩
      rw [← hx,heval] at hz
      exact hz
    · intro h y
      obtain ⟨x,hx⟩ := h y
      exact ⟨(QuotientAddGroup.mk' N) x,(heval x).trans hx⟩
  constructor
  · intro hn
    apply lt_of_le_of_ne (socle_correction_rank_le G p B S)
    intro hr
    obtain ⟨iso⟩ := @nonempty_linearEquiv_of_rank_eq (ZMod p) Q U
      (inferInstance : Semiring (ZMod p)) (inferInstance : AddCommMonoid Q) modQ freeQ
      (inferInstance : AddCommMonoid U) modU freeU inferInstance hr
    have hj : Function.Injective (fun x : Q => iso.symm (e x)) := iso.symm.injective.comp he
    have hse : Function.Surjective e := by
      intro y
      obtain ⟨x,hx⟩ := Finite.surjective_of_injective hj (iso.symm y)
      exact ⟨x,iso.symm.injective hx⟩
    exact hn (hsurj.mp hse)
  · intro hr hs
    let iso := LinearEquiv.ofBijective e ⟨he,hsurj.mpr hs⟩
    exact (ne_of_lt hr) iso.rank_eq

end LogicLineages.ModelsAlgebra.PGroups
