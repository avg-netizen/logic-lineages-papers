module
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartTargets
public import LogicLineages.ModelsAlgebra.PGroups.ZeroStageReduced
public import Mathlib.SetTheory.Cardinal.Finite
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem actual_divisible_part : Targets.actualDivisiblePart := by
  intro G _
  have hmax : ∀ S : AddSubgroup G, SubgroupDivisible S → S ≤ divisiblePart G := by
    intro S hS
    exact le_iSup_of_le ⟨S,hS⟩ le_rfl
  refine ⟨?_,hmax⟩
  intro n hn x
  have hle : divisiblePart G ≤ pStep n (divisiblePart G) := by
    apply iSup_le
    intro S z hz
    obtain ⟨y,hy⟩ := S.property n hn ⟨z,hz⟩
    exact ⟨(y:G),hmax S.val S.property y.property,congrArg Subtype.val hy⟩
  obtain ⟨y,hy,he⟩ := hle x.property
  exact ⟨⟨y,hy⟩,Subtype.ext he⟩

theorem infinite_divisible_socle_at_cuts : Targets.infiniteDivisibleSocleAtCuts := by
  intro G _ p hp hr α
  have hD := (actual_divisible_part G).1
  have hle := p_divisible_in_every_stage G p (divisiblePart G) (hD p hp) α
  have hinf : Infinite (pSocle p (divisiblePart G)) := by
    apply not_finite_iff_infinite.mp
    intro hf
    letI := hf
    have hlt := (rank_le_card (ZMod p) (pSocle p (divisiblePart G))).trans_lt
      Cardinal.mk_lt_aleph0
    exact (not_lt_of_ge hr) hlt
  letI := hinf
  let j : pSocle p (divisiblePart G) → pSocle p (transfiniteFiltration p α : AddSubgroup G) :=
    fun x => ⟨x,hle x.property.1,x.property.2⟩
  apply Infinite.of_injective j
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : pSocle p (transfiniteFiltration p α : AddSubgroup G) => (z:G)) h

end LogicLineages.ModelsAlgebra.PGroups
