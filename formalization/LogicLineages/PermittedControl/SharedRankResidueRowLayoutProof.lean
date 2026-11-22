module
public import LogicLineages.PermittedControl.SharedRankResidueRowTargets
import LogicLineages.PermittedControl.MixedRankResidueStatementChecks
import LogicLineages.PermittedControl.RankResidueChoicesStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.SharedRankResidueRow
open PreparedProjection
open MixedRankResidue (rankSupport)
open StatementChecks (fixed_mixedRankResidueSupport fixed_rankResidueLayoutAndChoices)

theorem commonLayoutExact : CommonLayoutExact := by
  intro rows
  let terms := rows.flatMap (fun r => r.2.2)
  have keys : (commonLayout rows).map Prod.snd = rankSupport terms :=
    (fixed_rankResidueLayoutAndChoices.2.2.1 (rankSupport terms)).1
  have places : (commonLayout rows).map Prod.fst = (List.range (rankSupport terms).length).map Nat.succ :=
    (fixed_rankResidueLayoutAndChoices.2.2.1 (rankSupport terms)).2
  have support := fixed_mixedRankResidueSupport.1 terms
  refine ⟨?_,?_,?_,?_⟩
  · rw [places]
    exact List.Nodup.map Nat.succ_injective List.nodup_range
  · rw [keys]
    exact support.1
  · intro slot present
    have appears : slot.1 ∈ (commonLayout rows).map Prod.fst := List.mem_map.mpr ⟨slot,present,rfl⟩
    rw [places] at appears
    obtain ⟨i,_,same⟩ := List.mem_map.mp appears
    rw [← same]
    exact Nat.succ_pos i
  · intro rank
    rw [keys,support.2]
    constructor
    · rintro ⟨t,present,atRank⟩
      obtain ⟨r,inRows,inRow⟩ := List.mem_flatMap.mp present
      exact ⟨r,inRows,((fixed_mixedRankResidueSupport.1 r.2.2).2 rank).mpr ⟨t,inRow,atRank⟩⟩
    · rintro ⟨r,inRows,atRank⟩
      obtain ⟨t,inRow,atRank⟩ := ((fixed_mixedRankResidueSupport.1 r.2.2).2 rank).mp atRank
      exact ⟨t,List.mem_flatMap.mpr ⟨r,inRows,inRow⟩,atRank⟩

end LogicLineages.PermittedControl.SharedRankResidueRow
