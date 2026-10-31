module
public import LogicLineages.ModelsAlgebra.PGroups.StableStageTargets
public import LogicLineages.ModelsAlgebra.PGroups.DivisiblePartProof
public import LogicLineages.ModelsAlgebra.PGroups.CountableReducedZeroProof
public import LogicLineages.ModelsAlgebra.PGroups.SocleUlmVanishing
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups

theorem primary_stable_stage : Targets.primaryStableStage := by
  intro G _ p _ hp α hs
  let S : AddSubgroup G := transfiniteFiltration p α
  have hprimary : ∀ x:S,∃k:ℕ,p^k • x=0 := by
    intro x
    obtain ⟨k,hk⟩ := hp x
    exact ⟨k,Subtype.ext hk⟩
  have hsur : ∀x:S,∃y:S,p • y=x := by
    intro x
    have hx : (x:G)∈transfiniteFiltration p (α+1) := by
      rw [←hs]
      exact x.property
    rw [transfiniteFiltration_add_one] at hx
    obtain ⟨y,hy,he⟩ := hx
    exact ⟨⟨y,hy⟩,Subtype.ext he⟩
  have hd : SubgroupDivisible S := p_primary_divisible_from_p_surjective S p hprimary hsur
  have hmax : ∀β:Ordinal.{0}, divisiblePart G ≤ (transfiniteFiltration p β:AddSubgroup G) := by
    intro β
    exact p_divisible_in_every_stage G p (divisiblePart G)
      ((actual_divisible_part G).1 p (Fact.out : p.Prime).ne_zero) β
  have he : S=divisiblePart G := le_antisymm ((actual_divisible_part G).2 S hd) (hmax α)
  refine ⟨hd,he,?_⟩
  intro β hβ
  have hb : (transfiniteFiltration p β:AddSubgroup G)=divisiblePart G :=
    le_antisymm ((transfiniteFiltration_antitone p hβ).trans he.le) (hmax β)
  refine ⟨hb,?_⟩
  apply (GroupInfinitary.ulm_rank_zero_socle p G _).mpr
  intro x hx
  rw [hb] at hx ⊢
  obtain ⟨y,hy⟩ := (actual_divisible_part G).1 p (Fact.out : p.Prime).ne_zero ⟨x,hx.1⟩
  exact ⟨(y:G),y.property,congrArg Subtype.val hy⟩
end LogicLineages.ModelsAlgebra.PGroups
